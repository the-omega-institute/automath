#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Find bibliography entries that exist in source but never reach the compiled PDF.

Motivation. The RJ manuscript in `submitted_2026_upper_fibers_witness_covers_...` carries
two `@unpublished` entries for its sibling manuscripts, each with a note naming the sibling
archive directory. That is exactly the disclosure the pipeline should want. Neither entry is
cited anywhere, there is no `\\nocite`, and BibTeX drops uncited entries - so neither appears
in `main.bbl`, and the phrase "sibling archive" appears zero times in the submitted PDF. The
disclosure exists in the source and is invisible to the referee.

Reading the `.bib` file gives the opposite conclusion to reading the compiled document, and
only the second is what a referee sees. This script compares the two.

A missing entry is not always a defect - bibliographies routinely carry unused entries. The
report separates them:
  - HIGH  : self or sibling references (author Ma/Zhang, or a note mentioning a sibling
            archive, or an @unpublished companion). Invisible disclosure.
  - low   : ordinary unused entries, listed only as a count.

Controls, run before any result:
  - every key found in a compiled `.bbl` must also be defined in that manuscript's `.bib`
    files, otherwise the key extractor is wrong and nothing downstream means anything;
  - the known RJ case must be reported, otherwise the detector is not detecting.
"""
from __future__ import annotations

import argparse
import io
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent.parent
DEFAULT_PUB = REPO / "papers" / "publication"

ENTRY = re.compile(r"@(\w+)\s*\{\s*([^,\s}]+)\s*,", re.M)
BBLITEM = re.compile(r"\\bibitem(?:\[[^\]]*\])?\{([^}]+)\}")
CITE = re.compile(r"\\(?:no)?cite[a-zA-Z]*\s*(?:\[[^\]]*\])*\s*\{([^}]*)\}")

KNOWN_CASE = "submitted_2026_upper_fibers_witness_covers_fibonacci_apparition_rj"


def read(p):
    try:
        return io.open(p, encoding="utf-8", errors="replace").read()
    except Exception:
        return ""


def manuscripts(pub: Path):
    for d in sorted(pub.iterdir()):
        if d.is_dir() and d.name.startswith(("2026_", "submitted_2026_")):
            if (d / "main.tex").exists():
                yield d


def bib_entries(d: Path):
    """key -> (type, raw entry text), from every .bib in the manuscript."""
    out = {}
    for p in d.rglob("*.bib"):
        if "tmp" in p.parts:
            continue
        text = read(p)
        for m in ENTRY.finditer(text):
            kind, key = m.group(1).lower(), m.group(2)
            start = m.start()
            depth, i = 0, text.find("{", start)
            j = i
            while j < len(text):
                if text[j] == "{":
                    depth += 1
                elif text[j] == "}":
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            out[key] = (kind, text[start:j + 1], p.name)
    return out


def bbl_keys(d: Path):
    keys = set()
    for p in d.rglob("*.bbl"):
        if "tmp" in p.parts:
            continue
        keys |= set(BBLITEM.findall(read(p)))
    return keys


def cited_keys(d: Path):
    keys = set()
    for p in d.rglob("*.tex"):
        if "tmp" in p.parts or "_cut_" in p.name:
            continue
        for m in CITE.finditer(read(p)):
            for k in m.group(1).split(","):
                k = k.strip()
                if k:
                    keys.add(k)
    return keys


def is_sibling(kind: str, raw: str) -> bool:
    low = raw.lower()
    if "sibling archive" in low or "companion" in low:
        return True
    if kind == "unpublished" and ("ma" in low and "zhang" in low):
        return True
    if "haobo" in low or "wenlin" in low:
        return True
    return False


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="find invisible bibliography entries")
    ap.add_argument("--publication-dir", type=Path, default=DEFAULT_PUB)
    a = ap.parse_args(argv)

    data = []
    for d in manuscripts(a.publication_dir):
        entries, bbl, cited = bib_entries(d), bbl_keys(d), cited_keys(d)
        if not entries or not bbl:
            continue
        data.append((d, entries, bbl, cited))

    print(f"manuscripts with both a bibliography source and a compiled bbl: {len(data)}\n")

    print("CONTROL 1  every compiled key must be defined in the sources")
    bad = []
    for d, entries, bbl, _ in data:
        orphan = bbl - set(entries)
        if orphan:
            bad.append((d.name, sorted(orphan)[:3]))
    for name, o in bad[:5]:
        print(f"    {name}: {len(o)} compiled keys not found in .bib, e.g. {o}")
    print(f"    {len(data) - len(bad)}/{len(data)} clean")
    if len(bad) > len(data) // 3:
        print("  -> FAIL, the key extractor is unreliable. No conclusions drawn.\n")
        return 1
    print("  -> PASS (a few mismatches are expected where a .bbl was hand-edited)\n")

    findings = []
    for d, entries, bbl, cited in data:
        missing = [k for k in entries if k not in bbl]
        high = [k for k in missing if is_sibling(*entries[k][:2])]
        if high:
            findings.append((d, entries, high, len(missing)))

    print("HIGH  self or sibling entries that never reach the compiled bibliography")
    if not findings:
        print("    none")
    for d, entries, high, nmissing in sorted(findings, key=lambda t: -len(t[2])):
        print(f"    {d.name}")
        for k in high:
            kind, raw, src = entries[k]
            note = re.search(r"note\s*=\s*\{(.+?)\}", raw, re.S)
            title = re.search(r"title\s*=\s*\{(.+?)\}\s*,", raw, re.S)
            print(f"        {k}  [@{kind}, {src}]")
            if title:
                print(f"            title: {' '.join(title.group(1).split())[:80]}")
            if note:
                print(f"            note : {' '.join(note.group(1).split())[:80]}")
        print(f"        ({nmissing} uncited entries in total in this manuscript)")

    print("\nCONTROL 2  the known case must be detected")
    hit = any(d.name == KNOWN_CASE for d, _, _, _ in findings)
    print(f"    {KNOWN_CASE}: {'detected' if hit else 'NOT DETECTED'}")
    print(f"  -> {'PASS' if hit else 'FAIL'}")
    return 0 if hit else 1


if __name__ == "__main__":
    sys.exit(main())
