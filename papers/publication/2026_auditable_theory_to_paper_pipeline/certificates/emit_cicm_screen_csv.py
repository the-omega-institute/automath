#!/usr/bin/env python3
"""Emit the CICM screened-corpus transcript as CSV.

The input JSON is a paper-local certificate, not a live web scraper.  This
script validates the row-level schema and writes the exact reviewer-facing CSV
columns requested for the CICM 2021--2025 comparison.
"""

import csv
import json
import sys
from pathlib import Path


HEADER = [
    "year",
    "venue",
    "title",
    "doi_or_arxiv",
    "included_excluded",
    "keyword_hit",
    "rationale",
]


def load_rows(path: Path):
    data = json.loads(path.read_text(encoding="utf-8"))
    rows = data.get("screened_papers")
    if not isinstance(rows, list) or not rows:
        raise SystemExit("missing nonempty screened_papers list")

    seen = set()
    has_included = False
    has_excluded = False
    for index, row in enumerate(rows, start=1):
        missing = [field for field in HEADER if not row.get(field)]
        if missing:
            raise SystemExit(f"screened_papers[{index}] missing fields: {missing}")
        decision = row["included_excluded"]
        if decision not in {"included", "excluded"}:
            raise SystemExit(
                f"screened_papers[{index}] has invalid decision {decision!r}"
            )
        has_included = has_included or decision == "included"
        has_excluded = has_excluded or decision == "excluded"
        key = (row["year"], row["venue"], row["title"], row["doi_or_arxiv"])
        if key in seen:
            raise SystemExit(f"duplicate screened row: {key}")
        seen.add(key)

    if not has_included or not has_excluded:
        raise SystemExit("screened_papers must contain included and excluded rows")
    return rows


def main(argv):
    if len(argv) != 2:
        raise SystemExit("usage: emit_cicm_screen_csv.py cicm_search_transcript.json")
    rows = load_rows(Path(argv[1]))
    writer = csv.DictWriter(sys.stdout, fieldnames=HEADER, lineterminator="\n")
    writer.writeheader()
    for row in rows:
        writer.writerow({field: row[field] for field in HEADER})


if __name__ == "__main__":
    main(sys.argv)
