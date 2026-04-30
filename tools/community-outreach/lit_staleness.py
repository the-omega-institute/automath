#!/usr/bin/env python3
"""lit_staleness.py — Stage 0 literature-staleness checker for RESEARCH_BOARD.

Built after T-01 and T-08 turned out to be literature-closed AFTER codex burned
Stage A cycles. This tool runs BEFORE Stage A so codex skips closed problems.

Verdict ladder (per TODO):
  CLOSED            theorem proved/disproved; outreach value = 0; handoff Lean
  OVERTAKEN         AI tool / recent paper occupied the attack surface
  PARTIAL_PROGRESS  others have touched it; reframe attack plan
  FRESH             no recent activity; proceed
  UNCLEAR           mixed signals; human review needed

Sources consulted:
  - teorth/erdosproblems data/problems.yaml (status field per problem)
  - teorth/erdosproblems AI Contributions wiki (AI-touched problem numbers)
  - arXiv API (recent papers matching keywords from TODO title + statement)

Hard rules:
  - Read-only. No git mutations, no external posting.
  - Cached HTTP responses live in tools/community-outreach/lit_cache/ (gitignored).

Public API:
    check_todo(todo, registry, ai_refs, *, cache_dir) -> StalenessReport
    check_board(*, board_path, cache_dir, only_ids=None) -> list[StalenessReport]

CLI:
    lit_staleness.py                              # check all TODOs, print summary
    lit_staleness.py --json                       # emit JSON
    lit_staleness.py T-01 T-08 T-21               # check specific TODOs
    lit_staleness.py --refresh                    # bypass cache (force refetch)
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import time
import urllib.parse
import urllib.request
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable, Optional

REPO_ROOT = Path(__file__).resolve().parents[2]
BOARD_PATH_DEFAULT = REPO_ROOT / "tools/community-outreach/RESEARCH_BOARD.md"
CACHE_DIR_DEFAULT = REPO_ROOT / "tools/community-outreach/lit_cache"

ERDOS_YAML_URL = "https://raw.githubusercontent.com/teorth/erdosproblems/main/data/problems.yaml"
ERDOS_AI_WIKI_URL = "https://raw.githubusercontent.com/wiki/teorth/erdosproblems/AI-contributions-to-Erd%C5%91s-problems.md"
ARXIV_API = "http://export.arxiv.org/api/query"

# --- import the parser from dispatch_worktree.py to avoid duplication ---
sys.path.insert(0, str(Path(__file__).parent))
from dispatch_worktree import parse_board, TodoSpec  # noqa: E402


# ---------------------------------------------------------------------------
# Data model
# ---------------------------------------------------------------------------


@dataclass
class StalenessReport:
    todo_id: str
    title: str
    verdict: str
    confidence: int  # 1-5; 5 = high confidence
    rationale: str
    evidence: list[dict[str, str]] = field(default_factory=list)
    detected_papers: list[dict[str, str]] = field(default_factory=list)
    recommendation: str = ""
    checked_at: str = ""
    sources_checked: list[str] = field(default_factory=list)
    keywords_used: list[str] = field(default_factory=list)


# ---------------------------------------------------------------------------
# HTTP cache
# ---------------------------------------------------------------------------


def _cache_path(url: str, cache_dir: Path) -> Path:
    h = hashlib.sha256(url.encode("utf-8")).hexdigest()[:16]
    return cache_dir / f"{h}.txt"


def _fetch_arxiv_via_nyxid(url: str, *, timeout: int = 30) -> Optional[str]:
    """Try NyxID arxiv-api proxy. Returns None on any failure (caller falls back)."""
    import shutil, subprocess  # noqa: PLC0415
    nyxid = shutil.which("nyxid") or str(Path.home() / ".cargo/bin/nyxid")
    if not Path(nyxid).exists():
        return None
    # Strip ARXIV_API base prefix; pass only the relative path to the proxy.
    if not url.startswith(ARXIV_API):
        return None
    rel_path = url[len(ARXIV_API):]  # e.g. "?search_query=..."
    if not rel_path.startswith("?"):
        return None
    proxy_path = "/query" + rel_path
    try:
        proc = subprocess.run(
            [nyxid, "proxy", "request", "arxiv-api", proxy_path, "-m", "GET"],
            capture_output=True, text=True, timeout=timeout,
        )
        if proc.returncode == 0 and proc.stdout:
            return proc.stdout
    except Exception:  # noqa: BLE001
        pass
    return None


def cache_get(url: str, *, cache_dir: Path, max_age_hours: int = 24, force: bool = False, timeout: int = 30) -> str:
    cache_dir.mkdir(parents=True, exist_ok=True)
    p = _cache_path(url, cache_dir)
    if not force and p.exists() and (time.time() - p.stat().st_mtime) < max_age_hours * 3600:
        return p.read_text(encoding="utf-8")
    text: Optional[str] = None
    # Route arXiv calls through NyxID arxiv-api when available (audit logging,
    # polite-pool consistency). Falls back to direct urllib on any failure.
    if url.startswith(ARXIV_API):
        text = _fetch_arxiv_via_nyxid(url, timeout=timeout)
    if text is None:
        req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 (omega-lit-staleness/1.0)"})
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            text = resp.read().decode("utf-8", errors="replace")
    p.write_text(text, encoding="utf-8")
    return text


# ---------------------------------------------------------------------------
# Source loaders
# ---------------------------------------------------------------------------


def load_erdos_registry(*, cache_dir: Path, force: bool = False) -> dict[str, dict[str, str]]:
    """Map problem number → {state, prize, formal}."""
    text = cache_get(ERDOS_YAML_URL, cache_dir=cache_dir, force=force)
    out: dict[str, dict[str, str]] = {}
    for block in re.split(r"\n(?=- number:)", text):
        if not block.strip().startswith("- number"):
            continue
        num_m = re.search(r'number:\s*"([^"]+)"', block)
        state_m = re.search(r'state:\s*"([^"]+)"', block)
        prize_m = re.search(r'prize:\s*"([^"]+)"', block)
        if not num_m or not state_m:
            continue
        formal_m = re.search(r"formalized:[^\n]*\n\s*state:\s*\"([^\"]+)\"", block)
        out[num_m.group(1)] = {
            "state": state_m.group(1),
            "prize": prize_m.group(1) if prize_m else "",
            "formal": formal_m.group(1) if formal_m else "",
        }
    return out


def load_ai_wiki_refs(*, cache_dir: Path, force: bool = False) -> set[int]:
    """Set of Erdős problem numbers mentioned in the AI Contributions wiki."""
    text = cache_get(ERDOS_AI_WIKI_URL, cache_dir=cache_dir, force=force)
    refs: set[int] = set()
    for m in re.finditer(r"\[(\d{1,4})\]", text):
        refs.add(int(m.group(1)))
    return refs


def arxiv_search(query: str, *, cache_dir: Path, max_results: int = 15, force: bool = False) -> list[dict[str, str]]:
    """Hit arXiv API, parse Atom feed, return list of {title, url, published, summary}."""
    params = urllib.parse.urlencode(
        {
            "search_query": query,
            "sortBy": "submittedDate",
            "sortOrder": "descending",
            "max_results": str(max_results),
        }
    )
    url = f"{ARXIV_API}?{params}"
    try:
        text = cache_get(url, cache_dir=cache_dir, force=force, max_age_hours=12, timeout=20)
    except Exception as exc:  # noqa: BLE001
        return [{"error": f"arxiv api: {exc}", "title": "", "url": "", "published": ""}]
    entries: list[dict[str, str]] = []
    for chunk in re.split(r"<entry>", text)[1:]:
        end = chunk.find("</entry>")
        if end < 0:
            continue
        body = chunk[:end]
        title_m = re.search(r"<title>(.*?)</title>", body, re.DOTALL)
        id_m = re.search(r"<id>(.*?)</id>", body)
        pub_m = re.search(r"<published>(.*?)</published>", body)
        sum_m = re.search(r"<summary>(.*?)</summary>", body, re.DOTALL)
        if not title_m or not id_m or not pub_m:
            continue
        entries.append(
            {
                "title": re.sub(r"\s+", " ", title_m.group(1)).strip(),
                "url": id_m.group(1).strip(),
                "published": pub_m.group(1).strip()[:10],
                "summary": (re.sub(r"\s+", " ", sum_m.group(1)).strip()[:280] if sum_m else ""),
            }
        )
    return entries


# ---------------------------------------------------------------------------
# Keyword + Erdős detection
# ---------------------------------------------------------------------------


_STOPWORDS = {
    "erdos", "erdős", "this", "that", "with", "from", "they", "them", "what", "when",
    "have", "been", "here", "there", "such", "some", "into", "more", "than", "open",
    "problem", "conjecture", "question", "result", "theorem", "every", "exist",
    "exists", "given", "where", "which", "those", "above", "below", "form", "any",
    "all", "for", "the", "and", "are", "let", "set", "sets", "case", "cases",
    "value", "values", "function", "number", "numbers", "show", "prove",
    "verify", "verified", "true", "false", "small", "large", "first", "second",
    "still", "show", "shown", "yet",
}


def extract_keywords(todo: TodoSpec, n: int = 5) -> list[str]:
    """Extract n keywords from title + statement (LaTeX stripped)."""
    text = (todo.title or "") + " " + (todo.statement or "")[:600]
    # Strip LaTeX math
    text = re.sub(r"\$+[^$]*\$+", " ", text)
    text = re.sub(r"\\[a-zA-Z]+\s*", " ", text)
    text = re.sub(r"[^\w\s]", " ", text)
    words = re.findall(r"[A-Za-z]{4,}", text)
    seen: set[str] = set()
    keywords: list[str] = []
    for w in words:
        wl = w.lower()
        if wl in _STOPWORDS or wl in seen:
            continue
        seen.add(wl)
        keywords.append(w)
        if len(keywords) >= n:
            break
    return keywords


def detect_erdos_number(todo: TodoSpec) -> Optional[str]:
    for haystack in (todo.title, todo.source):
        m = re.search(r"Erd[őo]?s\s*#(\d+)", haystack or "")
        if m:
            return m.group(1)
        m = re.search(r"erdosproblems\.com/(\d+)", haystack or "")
        if m:
            return m.group(1)
    return None


def detect_arxiv_id(todo: TodoSpec) -> Optional[str]:
    for haystack in (todo.title, todo.source):
        m = re.search(r"arxiv\.org/abs/(\d{4}\.\d{4,6})", haystack or "", re.IGNORECASE)
        if m:
            return m.group(1)
        m = re.search(r"arxiv:(\d{4}\.\d{4,6})", haystack or "", re.IGNORECASE)
        if m:
            return m.group(1)
    return None


def collect_arxiv_ids_from_prior(todo: TodoSpec) -> list[tuple[str, int]]:
    """Pull every arxiv:YYYY.NNNNN reference out of the prior block + raw block.

    Returns list of (arxiv_id, year). Used to detect that the board already
    cites recent papers, even when keyword search misses them.
    """
    haystack = (todo.prior or "") + " " + (todo.raw_block or "")
    out: list[tuple[str, int]] = []
    seen: set[str] = set()
    for m in re.finditer(r"arxiv[:.]?(\d{4})\.(\d{4,6})", haystack, re.IGNORECASE):
        aid = f"{m.group(1)}.{m.group(2)}"
        if aid in seen:
            continue
        seen.add(aid)
        # arxiv IDs YYMM.NNNNN since 2007: first 2 chars = year offset from 2000
        year = 2000 + int(aid[:2])
        out.append((aid, year))
    return out


def board_status_signal(todo: TodoSpec) -> tuple[str, str] | None:
    """Read board status field; short-circuit if it already declares closed/overtaken."""
    s = (todo.status or "").lower()
    if not s:
        return None
    if "literature closed" in s or "literature overtaken" in s:
        return ("CLOSED" if "closed" in s else "OVERTAKEN", todo.status)
    if "handoff to lean4" in s or "not outreach" in s:
        return ("CLOSED", todo.status)
    if "stage a done" in s and ("overtaken" in s or "narrow" in s):
        return ("OVERTAKEN", todo.status)
    return None


# ---------------------------------------------------------------------------
# Per-TODO checker
# ---------------------------------------------------------------------------


def _today() -> str:
    return datetime.now(timezone.utc).date().isoformat()


def check_todo(
    todo: TodoSpec,
    *,
    registry: dict[str, dict[str, str]],
    ai_refs: set[int],
    cache_dir: Path,
    arxiv_year_floor: int = 2024,
) -> StalenessReport:
    evidence: list[dict[str, str]] = []
    detected: list[dict[str, str]] = []
    sources: list[str] = []
    keywords = extract_keywords(todo)

    erdos_num = detect_erdos_number(todo)
    arxiv_id = detect_arxiv_id(todo)

    # 0. Board self-declaration short-circuit
    board_signal = board_status_signal(todo)
    if board_signal:
        verdict, status_text = board_signal
        evidence.append({"src": "board status field", "note": status_text, "url": ""})
        sources.append("board status field")
        rec = "respect board self-declaration; do not redispatch"
        rationale = f"board status field: '{status_text}'"
        return StalenessReport(
            todo_id=todo.todo_id, title=todo.title, verdict=verdict, confidence=5,
            rationale=rationale, evidence=evidence, detected_papers=[],
            recommendation=rec, checked_at=_today(), sources_checked=sources, keywords_used=keywords,
        )

    # 0.5. Prior-section arxiv IDs
    prior_ids = collect_arxiv_ids_from_prior(todo)
    recent_prior_ids = [(aid, yr) for aid, yr in prior_ids if yr >= arxiv_year_floor]
    if recent_prior_ids:
        sources.append("board prior block")
        for aid, yr in recent_prior_ids[:5]:
            evidence.append(
                {
                    "src": "board prior block",
                    "note": f"cites arXiv:{aid} ({yr}+)",
                    "url": f"https://arxiv.org/abs/{aid}",
                }
            )

    # 1. Erdős registry check
    state = ""
    formal = ""
    if erdos_num:
        info = registry.get(erdos_num, {})
        state = info.get("state", "unknown")
        formal = info.get("formal", "")
        sources.append("erdosproblems registry")
        evidence.append(
            {
                "src": "erdosproblems registry",
                "note": f"#{erdos_num} state={state}, formalized={formal}",
                "url": f"https://www.erdosproblems.com/{erdos_num}",
            }
        )

    # 2. AI wiki check
    ai_touched = bool(erdos_num and int(erdos_num) in ai_refs)
    if erdos_num:
        sources.append("erdosproblems AI wiki")
        evidence.append(
            {
                "src": "erdosproblems AI wiki",
                "note": f"AI-touched={ai_touched}",
                "url": "https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems",
            }
        )

    # 3. arXiv keyword search 2024+: try a couple of widening strategies
    clean_papers: list[dict[str, str]] = []
    if keywords:
        # Strategy A: top-2 keywords AND'd
        if len(keywords) >= 2:
            qa = " AND ".join(f"all:\"{kw}\"" for kw in keywords[:2])
            qa += f" AND submittedDate:[{arxiv_year_floor}01010000 TO 202612312359]"
            clean_papers = [p for p in arxiv_search(qa, cache_dir=cache_dir, max_results=10) if not p.get("error")]
        # Strategy B: top-1 keyword alone (broader)
        if not clean_papers:
            qb = f"all:\"{keywords[0]}\" AND submittedDate:[{arxiv_year_floor}01010000 TO 202612312359]"
            clean_papers = [p for p in arxiv_search(qb, cache_dir=cache_dir, max_results=10) if not p.get("error")]
        sources.append(f"arxiv (keyword search, year>={arxiv_year_floor})")
        detected = clean_papers[:6]

    # 4. arXiv: also seek follow-ups citing the original paper (for arXiv-source TODOs)
    if arxiv_id and not erdos_num:
        # Search for "arxiv_id" in titles/abstracts of newer papers — proxy for citations
        followup_q = f"all:\"{arxiv_id}\" AND submittedDate:[{arxiv_year_floor}01010000 TO 202612312359]"
        try:
            followups = arxiv_search(followup_q, cache_dir=cache_dir, max_results=5)
            followups = [p for p in followups if not p.get("error") and arxiv_id not in p["url"]]
            if followups:
                sources.append(f"arxiv follow-up search on {arxiv_id}")
                for fp in followups[:3]:
                    detected.append({**fp, "_followup": "yes"})
        except Exception:
            pass

    # ---- Verdict ----
    verdict, confidence, rationale, recommendation = _decide_verdict(
        state=state,
        formal=formal,
        ai_touched=ai_touched,
        recent_papers=detected,
        has_erdos_num=bool(erdos_num),
        has_arxiv_id=bool(arxiv_id),
        recent_prior_count=len(recent_prior_ids),
    )

    return StalenessReport(
        todo_id=todo.todo_id,
        title=todo.title,
        verdict=verdict,
        confidence=confidence,
        rationale=rationale,
        evidence=evidence,
        detected_papers=detected,
        recommendation=recommendation,
        checked_at=_today(),
        sources_checked=sources,
        keywords_used=keywords,
    )


_CLOSED_STATES = {"proved", "disproved", "solved", "proved (Lean)", "disproved (Lean)", "solved (Lean)"}
_FINITE_STATES = {"verifiable", "falsifiable", "decidable"}


def _decide_verdict(
    *,
    state: str,
    formal: str,
    ai_touched: bool,
    recent_papers: list[dict[str, str]],
    has_erdos_num: bool,
    has_arxiv_id: bool,
    recent_prior_count: int = 0,
) -> tuple[str, int, str, str]:
    n_papers = len(recent_papers)

    # 1. Erdős registry says closed → CLOSED, high confidence
    if state in _CLOSED_STATES:
        return (
            "CLOSED",
            5,
            f"erdosproblems registry state='{state}' — theorem already established",
            "drop from outreach; if Lean formalization absent, hand off to lean4-formalize",
        )

    # 1.5. Board prior already cites ≥2 recent (>=2024) papers → likely overtaken
    if recent_prior_count >= 2:
        return (
            "PARTIAL_PROGRESS",
            4,
            f"board prior already cites {recent_prior_count} 2024+ papers (lit-active)",
            "review prior list; ensure attack plan does not duplicate cited follow-ups",
        )

    # 2. Independent / not provable / decided in special way → UNCLEAR (logic edge)
    if state in {"independent", "not provable", "not disprovable"}:
        return ("UNCLEAR", 3, f"registry state='{state}' — set-theoretic territory", "human review")

    # 3. open / verifiable / falsifiable / decidable → check AI + recent papers
    has_ai_ref = ai_touched
    has_followups = any(p.get("_followup") == "yes" for p in recent_papers)
    n_recent = sum(1 for p in recent_papers if not p.get("_followup"))

    if has_ai_ref and n_papers >= 2:
        return (
            "OVERTAKEN",
            4,
            f"AI wiki references this problem AND {n_papers} recent paper(s) found",
            "review AI wiki entry + most recent paper; reframe attack plan to avoid duplication",
        )
    if has_ai_ref:
        return (
            "PARTIAL_PROGRESS",
            3,
            "AI wiki already references this problem (no recent paper detected)",
            "review AI wiki entry; reframe to non-overlapping angle",
        )
    if has_followups:
        return (
            "OVERTAKEN",
            3,
            "follow-up papers cite the original arXiv source",
            "review follow-ups; reframe to avoid duplication",
        )
    if state in _FINITE_STATES and n_recent >= 3:
        return (
            "PARTIAL_PROGRESS",
            3,
            f"finite-buckets state='{state}' but {n_recent} recent papers in keyword space",
            "scan top recent papers before Stage A; ensure attack remains novel",
        )
    if n_recent >= 4:
        return (
            "PARTIAL_PROGRESS",
            3,
            f"{n_recent} recent papers in keyword space",
            "scan top recent papers before Stage A",
        )
    if state in _FINITE_STATES or state == "open":
        return ("FRESH", 4, f"registry state='{state}', no major recent activity in keyword space", "proceed")
    if not has_erdos_num and has_arxiv_id and n_recent <= 2 and not has_followups:
        return ("FRESH", 3, "arXiv-source TODO; no follow-ups, low keyword activity", "proceed")
    if not has_erdos_num and not has_arxiv_id and n_recent <= 2:
        return ("FRESH", 3, "non-registry TODO; low keyword activity", "proceed; human-verify recent papers")
    return ("UNCLEAR", 2, "mixed signals", "human review needed")


# ---------------------------------------------------------------------------
# Board scan
# ---------------------------------------------------------------------------


def check_board(
    *,
    board_path: Path = BOARD_PATH_DEFAULT,
    cache_dir: Path = CACHE_DIR_DEFAULT,
    only_ids: Optional[Iterable[str]] = None,
    force_refresh: bool = False,
    arxiv_year_floor: int = 2024,
) -> list[StalenessReport]:
    todos = parse_board(board_path)
    registry = load_erdos_registry(cache_dir=cache_dir, force=force_refresh)
    ai_refs = load_ai_wiki_refs(cache_dir=cache_dir, force=force_refresh)
    selected = list(only_ids) if only_ids else sorted(todos.keys(), key=lambda x: int(x.split("-")[1]))
    reports: list[StalenessReport] = []
    for tid in selected:
        if tid not in todos:
            continue
        rep = check_todo(todos[tid], registry=registry, ai_refs=ai_refs, cache_dir=cache_dir, arxiv_year_floor=arxiv_year_floor)
        reports.append(rep)
    return reports


# ---------------------------------------------------------------------------
# CLI rendering
# ---------------------------------------------------------------------------


_VERDICT_GLYPH = {
    "CLOSED": "🔴 CLOSED",
    "OVERTAKEN": "🟠 OVERTAKEN",
    "PARTIAL_PROGRESS": "🟡 PARTIAL",
    "FRESH": "🟢 FRESH",
    "UNCLEAR": "⚪ UNCLEAR",
}


def render_summary(reports: list[StalenessReport]) -> str:
    lines = [f"# Lit-staleness summary ({len(reports)} TODOs, checked {_today()})\n"]
    counts: dict[str, int] = {}
    for r in reports:
        counts[r.verdict] = counts.get(r.verdict, 0) + 1
    lines.append("Verdict counts:")
    for v in ("CLOSED", "OVERTAKEN", "PARTIAL_PROGRESS", "FRESH", "UNCLEAR"):
        c = counts.get(v, 0)
        lines.append(f"  {_VERDICT_GLYPH[v]}  x {c}")
    lines.append("")
    lines.append("| TODO | verdict | conf | recommendation |")
    lines.append("|---|---|---|---|")
    for r in reports:
        lines.append(f"| {r.todo_id} | {_VERDICT_GLYPH[r.verdict]} | {r.confidence}/5 | {r.recommendation[:80]} |")
    return "\n".join(lines)


def render_detail(reports: list[StalenessReport]) -> str:
    out: list[str] = []
    for r in reports:
        out.append(f"\n## {r.todo_id} · {r.title}")
        out.append(f"verdict: **{_VERDICT_GLYPH[r.verdict]}**  conf: {r.confidence}/5")
        out.append(f"rationale: {r.rationale}")
        out.append(f"recommendation: {r.recommendation}")
        if r.keywords_used:
            out.append(f"keywords: {', '.join(r.keywords_used)}")
        if r.evidence:
            out.append("evidence:")
            for ev in r.evidence:
                out.append(f"  - [{ev['src']}] {ev['note']} ({ev.get('url','')})")
        if r.detected_papers:
            out.append("recent papers (most recent first):")
            for p in r.detected_papers[:5]:
                tag = " [follow-up]" if p.get("_followup") else ""
                out.append(f"  - {p.get('published','?')} | {p.get('title','?')[:90]}{tag}")
                out.append(f"    {p.get('url','')}")
    return "\n".join(out)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("todo_ids", nargs="*", help="TODO IDs to check (default: all)")
    parser.add_argument("--json", action="store_true", help="Emit JSON instead of markdown")
    parser.add_argument("--detail", action="store_true", help="Include per-TODO detail block")
    parser.add_argument("--refresh", action="store_true", help="Bypass cache, force refetch all sources")
    parser.add_argument("--year", type=int, default=2024, help="arXiv year floor")
    parser.add_argument("--board", default=str(BOARD_PATH_DEFAULT), help="Path to RESEARCH_BOARD.md")
    parser.add_argument("--cache-dir", default=str(CACHE_DIR_DEFAULT), help="HTTP cache directory")
    args = parser.parse_args(list(argv) if argv is not None else None)

    reports = check_board(
        board_path=Path(args.board),
        cache_dir=Path(args.cache_dir),
        only_ids=args.todo_ids if args.todo_ids else None,
        force_refresh=args.refresh,
        arxiv_year_floor=args.year,
    )
    if args.json:
        print(json.dumps([asdict(r) for r in reports], ensure_ascii=False, indent=2))
        return 0
    print(render_summary(reports))
    if args.detail:
        print(render_detail(reports))
    return 0


if __name__ == "__main__":
    sys.exit(main())
