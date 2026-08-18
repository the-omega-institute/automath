#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Numeric fingerprint check for manuscript overlap.

Motivation. `split_overlap_harness.py` decides overlap from shared claim markers, shared
theorem phrases and token Jaccard. That detector is lexical. It graded
`projection` against `single_primitive` as "weak or background overlap only" while the two
manuscripts produce numerically identical collision-moment sequences - verified by direct
computation, S_q(m+1) of one equalling S_q(m) of the other for q = 1..4 and m = 1..12. No
threshold on a lexical metric reaches that pair, because the evidence is numeric.

This script adds the missing axis. It extracts every integer sequence a manuscript prints in
its own source and reports sequences that appear in more than one manuscript. Two papers
displaying the same distinctive run of integers are describing the same object, whatever
their notation, titles or section structure.

Limits, stated plainly:
  - A manuscript that computes a sequence but never displays it is invisible here. This
    complements the lexical detector; it does not replace it.
  - Short or generic runs are noise, so a run must be long enough and varied enough to be
    reported. The thresholds are arguments, not universal truths.

Controls run before any result is reported:
  - the two sequences known to be present in `single_primitive` must be found there;
  - no sequence may be reported as shared unless it was found in at least two distinct
    manuscript directories.
"""
from __future__ import annotations

import argparse
import io
import json
import re
import sys
from collections import defaultdict
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent.parent
DEFAULT_PUB = REPO / "papers" / "publication"

# A run of integers separated by commas, optionally with LaTeX spacing between them.
# The repetition floor is derived from min_len rather than hardcoded: an earlier version
# fixed it at four, so --min-len silently did nothing below five. The controls caught it.
def run_pattern(min_len: int) -> re.Pattern:
    reps = max(1, min_len - 1)
    return re.compile(
        r"(?<![\d.])\d{1,9}(?:\s*(?:,|\\,|\\;|\\ )\s*\d{1,9}){" + str(reps) + r",}(?![\d.])"
    )

KNOWN = {
    "single_primitive second moments": (6, 14, 36),
    "single_primitive fibre maxima": (2, 2, 3, 4, 5, 6, 8, 10, 13, 16),
}


def paper_dirs(pub: Path):
    out = []
    for d in sorted(pub.iterdir()):
        if d.is_dir() and d.name.startswith(("2026_", "submitted_2026_")):
            if (d / "main.tex").exists():
                out.append(d)
    return out


def sequences(d: Path, min_len: int, min_distinct: int, min_max: int):
    """Every integer run displayed in this manuscript's own sources."""
    rx = run_pattern(min_len)
    found = defaultdict(list)
    for p in d.rglob("*.tex"):
        if "_cut_" in p.name or "tmp" in p.parts:
            continue
        try:
            text = io.open(p, encoding="utf-8", errors="replace").read()
        except Exception:
            continue
        for m in rx.finditer(text):
            nums = tuple(int(x) for x in re.findall(r"\d+", m.group(0)))
            if len(nums) < min_len:
                continue
            if len(set(nums)) < min_distinct:
                continue
            if max(nums) < min_max:
                continue
            if nums == tuple(range(nums[0], nums[0] + len(nums))):
                continue                      # a plain enumeration, not a fingerprint
            found[nums].append(f"{p.relative_to(d)}")
    return found


def controls(by_paper) -> bool:
    print("CONTROLS")
    ok = True
    sp = [k for k in by_paper if "single_primitive" in k]
    if not sp:
        print("    FAIL single_primitive not scanned at all")
        return False
    seqs = set(by_paper[sp[0]])
    for name, want in KNOWN.items():
        hit = any(want == s[:len(want)] or want == s for s in seqs)
        if not hit:
            ok = False
        print(f"    {name}: {'found' if hit else 'NOT FOUND'}  {want}")
    print(f"  -> {'PASS' if ok else 'FAIL'}\n")
    return ok


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="numeric fingerprint overlap check")
    ap.add_argument("--publication-dir", type=Path, default=DEFAULT_PUB)
    ap.add_argument("--min-len", type=int, default=5)
    ap.add_argument("--min-distinct", type=int, default=4)
    ap.add_argument("--min-max", type=int, default=10)
    ap.add_argument("--json", type=Path)
    a = ap.parse_args(argv)

    dirs = paper_dirs(a.publication_dir)
    print(f"manuscripts scanned: {len(dirs)}\n")
    by_paper = {d.name: sequences(d, a.min_len, a.min_distinct, a.min_max) for d in dirs}

    if not controls(by_paper):
        print("Controls failed - the extractor is not seeing sequences it must see.")
        print("No overlap conclusions drawn.")
        return 1

    owners = defaultdict(set)
    where = defaultdict(list)
    for name, seqs in by_paper.items():
        for s, files in seqs.items():
            owners[s].add(name)
            where[(name, s)] = files

    shared = {s: sorted(p) for s, p in owners.items() if len(p) > 1}
    print(f"SHARED SEQUENCES  ({len(shared)} runs appear in more than one manuscript)")
    rows = []
    for s in sorted(shared, key=lambda t: (-len(shared[t]), -len(t))):
        papers = shared[s]
        disp = ", ".join(str(x) for x in s[:10]) + (" ..." if len(s) > 10 else "")
        print(f"    [{disp}]")
        for p in papers:
            print(f"        {p}   ({'; '.join(where[(p, s)][:2])})")
        rows.append({"sequence": list(s), "papers": papers})

    if not shared:
        print("    none")

    total = sum(len(v) for v in by_paper.values())
    print(f"\n{total} distinct displayed runs across all manuscripts; "
          f"{len(shared)} are shared.")
    if a.json:
        json.dump(rows, io.open(a.json, "w", encoding="utf-8"), indent=2)
        print(f"written: {a.json}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
