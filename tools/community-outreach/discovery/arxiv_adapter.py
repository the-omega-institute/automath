#!/usr/bin/env python3
"""Adapter from arxiv_watch paper fetches to Stage A candidate rows."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict
from pathlib import Path
from typing import Optional

SCRIPT_DIR = Path(__file__).resolve().parent
OUTREACH_DIR = SCRIPT_DIR.parent
REPO_ROOT = OUTREACH_DIR.parents[1]
sys.path.insert(0, str(OUTREACH_DIR))

import arxiv_watch  # noqa: E402


def _query_label(categories: list[str], since: str) -> str:
    return f"arxiv since={since} categories={','.join(categories)}"


def _abstract_excerpt(summary: str, *, limit: int = 900) -> str:
    text = " ".join((summary or "").split())
    if len(text) <= limit:
        return text
    return text[: limit - 3].rstrip() + "..."


def fetch_arxiv_candidates(
    *,
    since: str = "14d",
    categories: Optional[list[str]] = None,
    max_results: int = 400,
    use_nyxid: bool = True,
) -> list[dict]:
    """Return arXiv papers in outreach_pipeline Stage A candidate schema.

    Each row has the same canonical keys as gh_search_repos output:
    repo, url, description, query.  `repo` is namespaced as arxiv:<id>, and
    source/title/raw are included for downstream arXiv-specific branching.
    """
    cats = categories or list(arxiv_watch.DEFAULT_CATEGORIES)
    since_dt = arxiv_watch._parse_since(since)
    papers = arxiv_watch.fetch_recent_papers(
        categories=cats,
        since=since_dt,
        max_results=max_results,
        use_nyxid=use_nyxid,
    )
    query = _query_label(cats, since)
    candidates: list[dict] = []
    seen: set[str] = set()
    for paper in papers:
        arxiv_id = paper.arxiv_id
        repo_id = f"arxiv:{arxiv_id}"
        if repo_id in seen:
            continue
        seen.add(repo_id)
        raw = asdict(paper)
        candidates.append(
            {
                "repo": repo_id,
                "url": paper.url or f"https://arxiv.org/abs/{arxiv_id}",
                "description": _abstract_excerpt(paper.summary),
                "query": query,
                "source": "arxiv",
                "title": paper.title,
                "raw": raw,
            }
        )
    return candidates


def main(argv: Optional[list[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="print arXiv Stage A candidates as JSON Lines")
    parser.add_argument("--since", default="14d")
    parser.add_argument("--categories", nargs="+")
    parser.add_argument("--max-results", type=int, default=400)
    parser.add_argument("--no-nyxid", action="store_true")
    args = parser.parse_args(argv)

    candidates = fetch_arxiv_candidates(
        since=args.since,
        categories=args.categories,
        max_results=args.max_results,
        use_nyxid=not args.no_nyxid,
    )
    for item in candidates:
        print(json.dumps(item, ensure_ascii=False))
    print(f"# {len(candidates)} candidates", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
