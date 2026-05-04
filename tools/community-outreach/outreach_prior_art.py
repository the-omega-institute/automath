#!/usr/bin/env python3
"""Read-only prior-art and outreach-history coverage checks."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
import warnings
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
OUTREACH_LOG = SCRIPT_DIR / "OUTREACH_LOG.md"

SCAN_ROOTS = (REPO_ROOT / "papers" / "publication", REPO_ROOT / "theory")
SKIP_PARTS = {".git", "__pycache__", "outreach_state", "logs", "drafts", "targets"}
MAX_HITS, SNIPPET_BEFORE, SNIPPET_AFTER, KEYWORD_MIN_LEN, DEFAULT_WALL_CLOCK_S = 40, 2, 4, 4, 10.0


def _git_ls_tex_files() -> list[Path]:
    roots = [str(path.relative_to(REPO_ROOT)) for path in SCAN_ROOTS if path.exists()]
    if not roots:
        return []
    try:
        proc = subprocess.run(
            ["git", "ls-files", "--cached", "--others", "--exclude-standard", "--", *roots],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            timeout=8,
            encoding="utf-8",
            errors="replace",
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired):
        return []
    if proc.returncode != 0:
        return []
    out: list[Path] = []
    for line in proc.stdout.splitlines():
        rel = line.strip()
        if not rel.endswith(".tex"):
            continue
        path = REPO_ROOT / rel
        if path.is_file() and not _is_explicitly_skipped(path):
            out.append(path)
    return sorted(set(out))


def _iter_tex_files() -> list[Path]:
    files = _git_ls_tex_files()
    if files:
        return files
    out: list[Path] = []
    for root in SCAN_ROOTS:
        if root.exists():
            out.extend(p for p in root.rglob("*.tex") if p.is_file() and not _is_explicitly_skipped(p))
    return sorted(out)


def _is_explicitly_skipped(path: Path) -> bool:
    try:
        rel_parts = path.relative_to(REPO_ROOT).parts
    except ValueError:
        rel_parts = path.parts
    return any(part in SKIP_PARTS for part in rel_parts)


def _camel_split(token: str) -> list[str]:
    spaced = re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", token)
    return [p for p in re.split(r"[^A-Za-z0-9]+", spaced) if p]


def _keywords_from(query: str) -> list[str]:
    keywords: set[str] = set()
    for token in re.findall(r"[A-Za-z0-9][A-Za-z0-9_.-]+", query or ""):
        cleaned = token.strip("._-").lower()
        if len(cleaned) >= KEYWORD_MIN_LEN:
            keywords.add(cleaned)
        for piece in _camel_split(token):
            piece = piece.lower()
            if len(piece) >= KEYWORD_MIN_LEN:
                keywords.add(piece)
    return sorted(keywords)


def _normalize_space(text: str) -> str:
    return re.sub(r"\s+", " ", text or "").strip().lower()


def _snippet(lines: list[str], idx: int) -> str:
    start = max(0, idx - SNIPPET_BEFORE)
    end = min(len(lines), idx + SNIPPET_AFTER + 1)
    return "\n".join(lines[start:end]).strip()


def _line_matches(line: str, query_norm: str, keywords: list[str]) -> bool:
    low = _normalize_space(line)
    if query_norm and query_norm in low:
        return True
    if not keywords:
        return False
    matched = [kw for kw in keywords if kw in low]
    if len(keywords) == 1:
        return bool(matched)
    # Multi-keyword queries require >=2 distinct keywords co-occurring on the
    # same line. The previous "any keyword >=8 chars" fallback was too loose
    # — common math terms ("extension", "fibonacci", "variable") would single-
    # handedly trigger matches on unrelated papers.
    return len(matched) >= 2


def find_paper_coverage(query: str) -> list[dict[str, object]]:
    """Search papers/publication/**/*.tex and theory/**/*.tex for coverage.

    Best-precision usage: pass a unique identifier (arxiv id, distinctive
    title phrase, theorem name). Keyword soups produce extra hits from
    unrelated papers whose labels happen to co-locate two generic terms.
    """
    query = (query or "").strip()
    if not query:
        return []
    query_norm = _normalize_space(query)
    keywords = _keywords_from(query)
    deadline = time.monotonic() + DEFAULT_WALL_CLOCK_S
    hits: list[dict[str, object]] = []

    for path in _iter_tex_files():
        if time.monotonic() > deadline:
            warnings.warn(
                "prior-art scan exceeded 10s; returning partial paper coverage hits",
                RuntimeWarning,
                stacklevel=2,
            )
            break
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        lines = text.splitlines()
        for idx, line in enumerate(lines):
            if _line_matches(line, query_norm, keywords):
                hits.append({"path": str(path.relative_to(REPO_ROOT)), "line": idx + 1, "snippet": _snippet(lines, idx)})
                if len(hits) >= MAX_HITS:
                    return hits
    return hits


def _target_needles(target_id_or_url: str) -> list[str]:
    raw = (target_id_or_url or "").strip()
    if not raw:
        return []
    needles = {raw.lower().rstrip("/")}
    compact = re.sub(r"^https?://", "", raw.lower()).rstrip("/")
    needles.add(compact)
    arxiv_m = re.search(r"arxiv\.org/(?:abs|pdf)/([0-9]{4}\.[0-9]{4,5})(?:v\d+)?", raw)
    if arxiv_m:
        arxiv_id = arxiv_m.group(1)
        needles.update({arxiv_id, f"arxiv:{arxiv_id}"})
    gh_m = re.search(r"github\.com/([^/\s]+/[^/\s]+)(?:/(issues|pull)/(\d+))?", raw)
    if gh_m:
        repo = gh_m.group(1).lower()
        needles.add(repo)
        if gh_m.group(2) and gh_m.group(3):
            needles.add(f"{repo}#{gh_m.group(3)}")
            needles.add(f"{repo}/{gh_m.group(2)}/{gh_m.group(3)}")
    return sorted(n for n in needles if n)


def find_outreach_history_coverage(target_id_or_url: str) -> list[dict[str, object]]:
    """Return OUTREACH_LOG rows that appear to match a prior engagement."""
    needles = _target_needles(target_id_or_url)
    if not needles or not OUTREACH_LOG.exists():
        return []
    try:
        lines = OUTREACH_LOG.read_text(encoding="utf-8", errors="replace").splitlines()
    except OSError:
        return []
    hits: list[dict[str, object]] = []
    for idx, line in enumerate(lines):
        low = line.lower()
        if any(needle in low for needle in needles):
            hits.append({"path": str(OUTREACH_LOG.relative_to(REPO_ROOT)), "line": idx + 1, "snippet": _snippet(lines, idx)})
    return hits[:MAX_HITS]


def _print_hits(label: str, hits: list[dict[str, object]]) -> None:
    if not hits:
        return
    print(f"\n## {label}")
    for hit in hits:
        print(f"\n{hit['path']}:{hit['line']}")
        print("```")
        print(str(hit["snippet"]).rstrip())
        print("```")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="outreach prior-art coverage check")
    parser.add_argument("query", help="paper title, topic, target id, or URL")
    parser.add_argument("--json", action="store_true", help="print machine-readable hits")
    args = parser.parse_args(argv)

    paper_hits = find_paper_coverage(args.query)
    history_hits = find_outreach_history_coverage(args.query)
    covered = bool(paper_hits or history_hits)

    if args.json:
        payload = {"paper": paper_hits, "outreach_history": history_hits, "covered": covered}
        print(json.dumps(payload, ensure_ascii=False, indent=2))
    elif covered:
        _print_hits("Paper Coverage", paper_hits)
        _print_hits("Outreach History Coverage", history_hits)
    else:
        print("(no prior paper or outreach-history coverage hits)", file=sys.stderr)
    return 1 if covered else 0


if __name__ == "__main__":
    raise SystemExit(main())
