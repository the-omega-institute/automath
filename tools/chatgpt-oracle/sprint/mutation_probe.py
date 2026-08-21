#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Ask what each verifier actually constrains, by changing the numbers it checks.

A script that exits 0 tells you it ran. It does not tell you that it would have objected had
the paper been wrong. At t545 two headline verifiers were probed by hand: cubical_stokes' box
formula flipped to FAIL when 2.0 became 2.1, and scan_projection's period-two constant flipped
when 953 became 954. Both are real constraints. This automates the same question.

METHOD. For each verify_*.py, find numeric literals of at least three significant digits, which
is where claimed constants live. Perturb one at a time, run the script, and see whether its
verdict changes. Restore immediately, whether or not the run succeeded.

READING THE RESULT. A script where no mutation changes the verdict is not necessarily wrong,
but it is not evidence either: it would have reported the same thing had the constant been
different. Those are listed as UNCONSTRAINED and are the ones worth reading by hand.

The baseline verdict is captured first. Scripts that already fail, or that time out, are
reported separately rather than being silently counted as constrained.
"""
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3] / "papers" / "publication"
# Claimed constants in these papers are often SMALL integers -- window6's whole
# result is the set {3, 6, 8, 9} and cell counts 21 and 48. A first version
# matched only three-or-more significant digits and so mutated array sizes and
# loop bounds instead, reporting almost everything as unconstrained. Match any
# numeric literal and try more of them.
NUM = re.compile(r'(?<![\w.])(\d+\.\d+|\d+)(?![\w.])')
TIMEOUT = 180
MAX_MUT = 8


def verdict(path):
    """(exit code, whether the output contains a failure word)."""
    try:
        r = subprocess.run([sys.executable, path.name], cwd=str(path.parent),
                           capture_output=True, text=True, timeout=TIMEOUT,
                           encoding="utf-8", errors="replace")
    except subprocess.TimeoutExpired:
        return ("TIMEOUT", "")
    out = (r.stdout or "") + (r.stderr or "")
    # Only an explicit verdict counts. Matching a bare 'False' read the legitimate
    # per-row False column of verify_refinement_family.py as a failing baseline.
    fail = bool(re.search(r'->\s*FAIL|FAILED|^FAIL', out, re.M))
    return (r.returncode, fail)


def perturb(tok):
    if "." in tok:
        head, tail = tok.rsplit(".", 1)
        return head + "." + tail[:-1] + ("1" if tail[-1] != "1" else "2")
    return tok[:-1] + ("1" if tok[-1] != "1" else "2")


def probe(path):
    src = path.read_text(encoding="utf-8", errors="replace")
    base = verdict(path)
    if base[0] == "TIMEOUT":
        return ("TIMEOUT", base, 0, 0)
    if base[0] != 0 or base[1]:
        return ("ALREADY-FAILING", base, 0, 0)
    spots = []
    for m in NUM.finditer(src):
        line = src[max(0, m.start() - 90):m.start()]
        if line.lstrip().startswith("#") or "0x" in line[-4:]:
            continue
        spots.append(m)
        if len(spots) >= MAX_MUT * 4:
            break
    tried = caught = 0
    try:
        for m in spots:
            if tried >= MAX_MUT:
                break
            new = src[:m.start()] + perturb(m.group(1)) + src[m.end():]
            if new == src:
                continue
            path.write_text(new, encoding="utf-8", newline="")
            tried += 1
            v = verdict(path)
            if v != base:
                caught += 1
    finally:
        path.write_text(src, encoding="utf-8", newline="")
    if tried == 0:
        return ("NO-LITERALS", base, 0, 0)
    return ("CONSTRAINED" if caught else "UNCONSTRAINED", base, tried, caught)


def main():
    pats = sys.argv[1:] or ["window6", "projection_ontological"]
    papers = [p for p in sorted(ROOT.glob("2026_*")) if any(s in p.name for s in pats)]
    if not papers:
        print("CONTROL FAILED: no papers matched", pats)
        return 2
    weak = []
    for paper in papers:
        scripts = sorted((paper / "artifacts").glob("verify_*.py"))
        print(f"\n{paper.name[5:]}  ({len(scripts)} scripts)")
        for s in scripts:
            tag, base, tried, caught = probe(s)
            print(f"    {tag:15s} {s.name:44s} mutations {caught}/{tried}")
            if tag in ("UNCONSTRAINED", "NO-LITERALS"):
                weak.append(f"{paper.name[5:30]}/{s.name}")
    print("\nscripts whose verdict no mutation changed:")
    for w in weak or ["    none"]:
        print("   ", w)
    print("\nUNCONSTRAINED does not mean wrong. It means the run is not evidence about the"
          "\nconstant, because it would have said the same thing had the constant differed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
