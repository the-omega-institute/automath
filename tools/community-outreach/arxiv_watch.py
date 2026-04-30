#!/usr/bin/env python3
"""arxiv_watch.py — Round 0 staleness booster: scan recent arXiv math papers
against active RESEARCH_BOARD targets.

Routes through NyxID `arxiv-api` custom service for audit logging. Falls back
to direct arxiv API if the NyxID service isn't configured (so the tool keeps
working even when the broker is offline).

Workflow:
    1. Pull last N days of math.NT / math.CO / math.AG / math.DS / math.LO
       (configurable via --categories) sorted by submittedDate desc.
    2. For each active TODO on the board, extract keywords (reuses
       lit_staleness.extract_keywords).
    3. For each (paper, todo) pair, score keyword overlap; emit hits when score
       crosses --min-overlap (default 2 keywords matched in title or abstract).
    4. Output: stdout summary + optional --json file.

CLI:
    arxiv_watch.py                          # last 7d, all active TODOs
    arxiv_watch.py --since 14d              # custom window
    arxiv_watch.py --categories math.NT     # narrow categories
    arxiv_watch.py --json out.json          # machine-readable output
    arxiv_watch.py --no-nyxid               # bypass NyxID, hit arxiv directly
    arxiv_watch.py --only T-10              # check single TODO

Hard rules per project memory:
    - Read-only. No git mutations, no posting.
    - Cache responses in tools/community-outreach/lit_cache/.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import urllib.parse
import urllib.request
from dataclasses import asdict, dataclass, field
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Optional

REPO_ROOT = Path(__file__).resolve().parents[2]
BOARD_PATH = REPO_ROOT / "tools/community-outreach/RESEARCH_BOARD.md"
CACHE_DIR = REPO_ROOT / "tools/community-outreach/lit_cache"
ARXIV_DIRECT = "http://export.arxiv.org/api/query"
NYXID_SLUG = "arxiv-api"

DEFAULT_CATEGORIES = ["math.NT", "math.CO", "math.AG", "math.DS", "math.LO", "math.PR"]

# Reuse machinery from lit_staleness
sys.path.insert(0, str(Path(__file__).parent))
from lit_staleness import extract_keywords as _base_extract_keywords  # noqa: E402
from dispatch_worktree import parse_board, TodoSpec  # noqa: E402


# Extra stopwords for arxiv_watch: generic math jargon that produces noise.
# A keyword in this set still counts toward overlap, but isn't enough on its own —
# every flagged hit must include at least one keyword OUTSIDE this set.
_GENERIC_MATH_TERMS = frozenset({
    "upper", "lower", "bound", "bounds", "bounded", "system", "systems", "complete",
    "completeness", "characterization", "characterize", "general", "generic", "generalized",
    "specific", "abstract", "applied", "estimate", "estimates", "approximation",
    "approximations", "conjecture", "conjectures", "asymptotic", "asymptotics",
    "explicit", "implicit", "quantitative", "qualitative", "uniform", "nonuniform",
    "linear", "nonlinear", "smooth", "discrete", "continuous", "finite", "infinite",
    "polynomial", "exponential", "rational", "integer", "integers", "real", "complex",
    "sharp", "tight", "weak", "strong", "structure", "structures", "structural",
    "theory", "theoretic", "study", "studies", "result", "results", "method", "methods",
    "approach", "approaches", "model", "models", "version", "versions", "variant",
    "variants", "regime", "regimes",
})


def extract_keywords(todo: TodoSpec, n: int = 8) -> list[str]:
    return _base_extract_keywords(todo, n=n)


def has_specific_match(matched: list[str]) -> bool:
    """True iff the match list contains at least one non-generic term."""
    return any(k.lower() not in _GENERIC_MATH_TERMS for k in matched)


def has_distinctive_term(matched: list[str]) -> bool:
    """A 'distinctive' term: proper noun (capitalised inside text), or a
    technical word ≥6 chars that isn't a generic math term. Used to
    auto-promote low-overlap hits that contain a clear specific signal
    like 'Walsh' or 'Liouville'.
    """
    for k in matched:
        if k.lower() in _GENERIC_MATH_TERMS:
            continue
        if k[:1].isupper() and not k.isupper():
            return True  # ProperNoun like Walsh, Leth, Sidon
        if len(k) >= 6:
            return True
    return False


# ---------------------------------------------------------------------------
# Data model
# ---------------------------------------------------------------------------


@dataclass
class ArxivPaper:
    arxiv_id: str
    title: str
    url: str
    published: str
    summary: str
    authors: list[str] = field(default_factory=list)
    primary_category: str = ""

    @property
    def abstract_blob(self) -> str:
        return f"{self.title} {self.summary}".lower()


@dataclass
class WatchHit:
    todo_id: str
    todo_title: str
    paper: ArxivPaper
    matched_keywords: list[str]
    overlap_score: int

    def to_dict(self) -> dict:
        d = asdict(self)
        d["paper"] = asdict(self.paper)
        return d


# ---------------------------------------------------------------------------
# arXiv fetch (NyxID-routed, with direct fallback)
# ---------------------------------------------------------------------------


def _nyxid_available() -> bool:
    if shutil.which("nyxid"):
        return True
    return (Path.home() / ".cargo/bin/nyxid").exists()


def _nyxid_bin() -> str:
    p = shutil.which("nyxid")
    return p or str(Path.home() / ".cargo/bin/nyxid")


def _arxiv_query_path(*, search_query: str, max_results: int) -> str:
    params = urllib.parse.urlencode({
        "search_query": search_query,
        "sortBy": "submittedDate",
        "sortOrder": "descending",
        "max_results": str(max_results),
    })
    return f"/query?{params}"


def fetch_via_nyxid(path: str, *, timeout: int = 30) -> str:
    cmd = [
        _nyxid_bin(),
        "proxy", "request", NYXID_SLUG, path,
        "-m", "GET",
    ]
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    if proc.returncode != 0:
        raise RuntimeError(f"NyxID arxiv proxy failed: {proc.stderr or proc.stdout}")
    return proc.stdout


def fetch_direct(path: str, *, timeout: int = 30) -> str:
    url = f"{ARXIV_DIRECT}{path[len('/query'):]}" if path.startswith("/query") else f"{ARXIV_DIRECT}?{path.lstrip('?')}"
    # path comes in as "/query?..." → strip "/query" prefix to fit ARXIV_DIRECT base
    req = urllib.request.Request(url, headers={"User-Agent": "automath-outreach/arxiv-watch"})
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return resp.read().decode("utf-8", errors="replace")


def fetch_arxiv(*, search_query: str, max_results: int = 50, use_nyxid: bool = True) -> str:
    """Return raw Atom XML."""
    path = _arxiv_query_path(search_query=search_query, max_results=max_results)
    if use_nyxid and _nyxid_available():
        try:
            return fetch_via_nyxid(path)
        except Exception as exc:  # noqa: BLE001
            print(f"WARN: NyxID arxiv fetch failed ({exc}); falling back to direct", file=sys.stderr)
    return fetch_direct(path)


# ---------------------------------------------------------------------------
# Atom parser
# ---------------------------------------------------------------------------


_ENTRY_SPLIT = re.compile(r"<entry>", re.IGNORECASE)
_ENTRY_END = "</entry>"


def parse_atom(xml: str) -> list[ArxivPaper]:
    chunks = _ENTRY_SPLIT.split(xml)[1:]
    out: list[ArxivPaper] = []
    for chunk in chunks:
        end = chunk.find(_ENTRY_END)
        if end < 0:
            continue
        body = chunk[:end]
        title_m = re.search(r"<title>(.*?)</title>", body, re.DOTALL)
        id_m = re.search(r"<id>(.*?)</id>", body)
        pub_m = re.search(r"<published>(.*?)</published>", body)
        sum_m = re.search(r"<summary>(.*?)</summary>", body, re.DOTALL)
        primary_m = re.search(r'<arxiv:primary_category[^>]+term="([^"]+)"', body)
        if not title_m or not id_m or not pub_m:
            continue
        url = id_m.group(1).strip()
        # arxiv id last path segment
        arxiv_id = url.rsplit("/", 1)[-1]
        authors = [a.strip() for a in re.findall(r"<name>(.*?)</name>", body)]
        out.append(ArxivPaper(
            arxiv_id=arxiv_id,
            title=re.sub(r"\s+", " ", title_m.group(1)).strip(),
            url=url,
            published=pub_m.group(1).strip()[:10],
            summary=re.sub(r"\s+", " ", (sum_m.group(1) if sum_m else "")).strip(),
            authors=authors,
            primary_category=primary_m.group(1) if primary_m else "",
        ))
    return out


# ---------------------------------------------------------------------------
# Match logic
# ---------------------------------------------------------------------------


def keyword_overlap(paper: ArxivPaper, keywords: list[str]) -> tuple[int, list[str]]:
    blob = paper.abstract_blob
    matched = [k for k in keywords if k.lower() in blob]
    return len(matched), matched


def fetch_recent_papers(
    *,
    categories: list[str],
    since: datetime,
    max_results: int = 100,
    use_nyxid: bool = True,
) -> list[ArxivPaper]:
    cat_clause = " OR ".join(f"cat:{c}" for c in categories)
    since_str = since.strftime("%Y%m%d%H%M")
    until_str = datetime.now(timezone.utc).strftime("%Y%m%d%H%M")
    search_query = f"({cat_clause}) AND submittedDate:[{since_str} TO {until_str}]"
    xml = fetch_arxiv(search_query=search_query, max_results=max_results, use_nyxid=use_nyxid)
    return parse_atom(xml)


def scan_board(
    *,
    todos: dict[str, TodoSpec],
    papers: list[ArxivPaper],
    min_overlap: int,
    only_active: bool = True,
) -> list[WatchHit]:
    hits: list[WatchHit] = []
    for tid, todo in todos.items():
        if only_active and (todo.status or "").upper() in {"CLOSED", "DONE", "OVERTAKEN"}:
            continue
        keywords = extract_keywords(todo, n=8)
        if not keywords:
            continue
        for paper in papers:
            score, matched = keyword_overlap(paper, keywords)
            # Two acceptance paths:
            #   A. score >= min_overlap AND has at least one non-generic term.
            #   B. score == 2 AND a distinctive term is present (auto-promote).
            if score < 2:
                continue
            accept_a = score >= min_overlap and has_specific_match(matched)
            accept_b = score >= 2 and has_distinctive_term(matched)
            if not (accept_a or accept_b):
                continue
            hits.append(WatchHit(
                todo_id=tid,
                todo_title=todo.title or "",
                paper=paper,
                matched_keywords=matched,
                overlap_score=score,
            ))
    hits.sort(key=lambda h: (-h.overlap_score, h.paper.published), reverse=False)
    # secondary sort: most recent first within same score
    hits.sort(key=lambda h: (-h.overlap_score, h.paper.published), reverse=True)
    return hits


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _parse_since(value: str) -> datetime:
    """Accept '7d', '24h', '2w', or ISO date."""
    now = datetime.now(timezone.utc)
    m = re.fullmatch(r"(\d+)\s*([dhw])", value.strip().lower())
    if m:
        n = int(m.group(1))
        unit = m.group(2)
        if unit == "d":
            return now - timedelta(days=n)
        if unit == "h":
            return now - timedelta(hours=n)
        if unit == "w":
            return now - timedelta(weeks=n)
    try:
        return datetime.fromisoformat(value).replace(tzinfo=timezone.utc)
    except ValueError as exc:
        raise SystemExit(f"--since must be like '7d', '48h', '2w', or YYYY-MM-DD ({exc})")


def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Scan recent arXiv papers vs RESEARCH_BOARD targets")
    p.add_argument("--since", default="7d", help="Time window: e.g. 7d, 48h, 2w, or YYYY-MM-DD")
    p.add_argument("--categories", nargs="+", default=DEFAULT_CATEGORIES,
                   help=f"arXiv categories (default: {' '.join(DEFAULT_CATEGORIES)})")
    p.add_argument("--max-results", type=int, default=100,
                   help="Max papers to pull per query (default: 100)")
    p.add_argument("--min-overlap", type=int, default=3,
                   help="Score threshold for path-A acceptance (default: 3). Score-2 hits "
                        "are still surfaced if they contain a distinctive term (proper noun "
                        "or 6+ char specific word).")
    p.add_argument("--only", action="append", default=[],
                   help="Only check these TODO ids (repeatable)")
    p.add_argument("--include-closed", action="store_true",
                   help="Also scan closed/done TODOs (default: skip)")
    p.add_argument("--no-nyxid", action="store_true",
                   help="Bypass NyxID, hit arxiv API directly")
    p.add_argument("--json", type=Path,
                   help="Write JSON report to this path")
    p.add_argument("--board", type=Path, default=BOARD_PATH,
                   help=f"Path to board (default: {BOARD_PATH.relative_to(REPO_ROOT)})")
    args = p.parse_args(argv)

    since_dt = _parse_since(args.since)
    todos = parse_board(args.board)
    if args.only:
        wanted = set(args.only)
        todos = {k: v for k, v in todos.items() if k in wanted}
        if not todos:
            print(f"No TODOs match: {args.only}", file=sys.stderr)
            return 1

    print(f"Fetching arXiv papers since {since_dt.strftime('%Y-%m-%d %H:%M UTC')} from "
          f"{', '.join(args.categories)}...", file=sys.stderr)
    papers = fetch_recent_papers(
        categories=args.categories,
        since=since_dt,
        max_results=args.max_results,
        use_nyxid=not args.no_nyxid,
    )
    print(f"Got {len(papers)} papers. Scanning {len(todos)} TODOs (min_overlap={args.min_overlap})...",
          file=sys.stderr)

    hits = scan_board(
        todos=todos,
        papers=papers,
        min_overlap=args.min_overlap,
        only_active=not args.include_closed,
    )

    # Console summary
    if not hits:
        print("\nNo overlapping papers detected. Board targets look fresh.")
    else:
        print(f"\n{len(hits)} hit(s) — recent papers overlap with active board targets:\n")
        for h in hits:
            print(f"  [{h.todo_id}] score={h.overlap_score} "
                  f"matched={','.join(h.matched_keywords)}")
            print(f"    paper:    {h.paper.title}")
            print(f"    arxiv:    {h.paper.url}  ({h.paper.published})")
            print(f"    primary:  {h.paper.primary_category}")
            if h.paper.authors:
                print(f"    authors:  {', '.join(h.paper.authors[:4])}"
                      f"{' et al.' if len(h.paper.authors) > 4 else ''}")
            print(f"    todo:     {h.todo_title}")
            print()

    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        report = {
            "generated_at": datetime.now(timezone.utc).isoformat(),
            "since": since_dt.isoformat(),
            "categories": args.categories,
            "papers_scanned": len(papers),
            "todos_scanned": len(todos),
            "min_overlap": args.min_overlap,
            "hits": [h.to_dict() for h in hits],
        }
        args.json.write_text(json.dumps(report, indent=2))
        print(f"\nJSON report: {args.json}", file=sys.stderr)

    return 0


if __name__ == "__main__":
    sys.exit(main())
