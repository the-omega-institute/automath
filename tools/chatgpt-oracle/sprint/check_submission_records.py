#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Check every submission record against the source it describes.

Three real defects were found by hand at t542-t543, all of the same kind: a file that records
a fact about the manuscript disagreed with the manuscript. A stale FAIL said the author block
was empty when both authors were declared; a page count of "about 35" had been scaled from
source line counts against a real build of 18; and a checklist listed two MSC codes that appear
nowhere in the paper. Nothing would have caught any of them on the next pass.

DESIGN NOTE, which is the whole point of this script.

Every check here can report three outcomes, never two:

    OK       record and source agree
    MISMATCH record and source disagree, with both values printed
    NOFIND   the check could not locate the thing in the source at all

NOFIND exists because that is how this session lost time repeatedly. A pattern written slightly
too narrowly returns empty, and empty is indistinguishable from clean unless it is given its own
name. Keywords written as \textbf{Keywords.} with a period were reported absent by a pattern
expecting a colon; MSC written as \textbf{MSC 2020:} was reported absent by a pattern expecting
\subjclass. Both papers were fine. The instrument was not.

So a NOFIND is a failure of this script, not a verdict about the paper, and it is printed as
loudly as a MISMATCH.
"""
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3] / "papers" / "publication"

BS = chr(92) + chr(92)   # a literal backslash inside a regex must itself be escaped
MSC_PAT = [BS + r'subjclass[[][^]]*[]][{]([^}]*)[}]',
           r'MSC[ ]*2020:?[}]?\s*([0-9A-Z, ]+)',
           r'Mathematics Subject Classifications?[.:]*[*]*[}]*\s*([0-9A-Z, ]+)']
KW_PAT = [BS + r'keywords[{]([^}]*)[}]',
          r'Keywords[.:][}]?[ ]*(.+)',
          r'Key words and phrases[.:][ ]*(.+)']
CODE = re.compile(r'\b\d{2}[A-Z]\d{2}\b')


def read(p):
    try:
        return p.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return ""


def first_match(text, pats):
    for pat in pats:
        m = re.search(pat, text, re.IGNORECASE)
        if m:
            return m.group(1).strip()
    return None


def pdf_pages(pdf):
    try:
        out = subprocess.run(["pdfinfo", str(pdf)], capture_output=True, text=True, timeout=60,
                             encoding="utf-8", errors="replace")
        m = re.search(r'Pages:\s*(\d+)', out.stdout)
        return int(m.group(1)) if m else None
    except Exception:
        return None


def pdf_text(pdf, page1=True):
    try:
        cmd = ["pdftotext", "-enc", "UTF-8"]
        if page1:
            cmd += ["-f", "1", "-l", "1"]
        cmd += [str(pdf), "-"]
        return subprocess.run(cmd, capture_output=True, text=True, timeout=120,
                              encoding="utf-8", errors="replace").stdout or ""
    except Exception:
        return ""


def check(paper):
    rows = []
    tex = read(paper / "main.tex")
    for extra in sorted(paper.glob("*.tex")):
        if extra.name != "main.tex":
            tex += "\n" + read(extra)
    pdf = paper / "main.pdf"
    meta = read(paper / "submission_metadata.md")
    ckl = read(paper / "submission_checklist.md")
    records = {"metadata": meta, "checklist": ckl}

    # --- pages -------------------------------------------------------------
    actual = pdf_pages(pdf)
    if actual is None:
        rows.append(("NOFIND", "pages", "no main.pdf or pdfinfo failed"))
    else:
        for name, txt in records.items():
            # Accept 'N pages' and 'N-page', and also \@abspage@last{N}: a checklist
            # writing 'a 17-page XeTeX output' was reported NOFIND by the narrower pattern.
            claims = [int(x) for x in re.findall(r'(\d+)[ -]pages?', txt)]
            claims += [int(x) for x in re.findall(r'abspage@last[{](\d+)[}]', txt)]
            if not claims:
                rows.append(("NOFIND", f"pages/{name}", "record states no page count"))
            elif actual in claims:
                rows.append(("OK", f"pages/{name}", f"{actual}"))
            else:
                # No tolerance. An engine-qualified record must ENUMERATE its counts, and the
                # build must equal one of them exactly. A +/-1 slack was tried first and it
                # silently accepted a checklist claiming 8 pages against a 9-page build, which
                # is the failure where the tolerance rather than the record decides the verdict.
                rows.append(("MISMATCH", f"pages/{name}",
                             f"pdf={actual} record={claims}"))

    # --- MSC ---------------------------------------------------------------
    # Take a window after the marker and harvest codes from it, rather than a
    # character class. The class approach stopped at the first ';' and read only
    # one code from 'Primary 11B39; Secondary 11A07, 11Y55, 68Q45', reporting a
    # MISMATCH against a record that was correct.
    _m = first_match(tex, MSC_PAT)
    _i = tex.find(_m) if _m else -1
    src_msc = set(CODE.findall(tex[_i:_i + 140])) if _i >= 0 else set()
    if not src_msc:
        rows.append(("NOFIND", "msc/source", "no MSC codes located in any .tex"))
    else:
        for name, txt in records.items():
            # The record side must accept every spelling the source side does. It first
            # matched only a literal 'MSC', so metadata writing 'Mathematics Subject
            # Classification' was reported NOFIND and a stale line went unseen.
            m = re.search(r'(MSC|Mathematics Subject Classifications?)[.: ]*(.*)', txt)
            rec = set(CODE.findall(m.group(0))) if m else set()
            if not rec:
                rows.append(("NOFIND", f"msc/{name}", "record states no MSC codes"))
            elif rec == src_msc:
                rows.append(("OK", f"msc/{name}", ",".join(sorted(src_msc))))
            else:
                rows.append(("MISMATCH", f"msc/{name}",
                             f"source={sorted(src_msc)} record={sorted(rec)}"))

    # --- keywords ----------------------------------------------------------
    kw = first_match(tex, KW_PAT)
    rows.append(("OK", "keywords", kw[:60]) if kw else
                ("NOFIND", "keywords", "no keyword line located in any .tex"))

    # --- authors -----------------------------------------------------------
    names = re.findall(BS + r'author[{]([^}' + BS + r']*)', tex)
    names = [n.strip() for n in names if n.strip()]
    if not names:
        names = re.findall(r'([A-Z][a-z]+[ ]+[A-Z][a-z]+)' + BS + r'thanks', tex)
    page1 = pdf_text(pdf)
    if not names:
        rows.append(("NOFIND", "authors", "no \author content located"))
    else:
        missing = [n for n in names if n.split()[-1].lower() not in page1.lower()]
        rows.append(("OK", "authors", "; ".join(names)) if not missing else
                    ("MISMATCH", "authors", f"declared={names} not rendered={missing}"))

    # --- target journal ----------------------------------------------------
    tgt = re.search(r'Primary target:\s*([^\n]+)', meta)
    letters = list(paper.glob("cover_letter*"))
    if not tgt:
        rows.append(("NOFIND", "target", "metadata states no Primary target"))
    elif not letters:
        rows.append(("MISMATCH", "target", f"metadata={tgt.group(1).strip()} but no cover letter"))
    else:
        rows.append(("OK", "target", f"{tgt.group(1).strip()} -> {letters[0].name}"))
    return rows


def main():
    SPRINT = ("window6", "projection_ontological", "brocot_condensation",
          "zeckendorf_stable", "scan_projection", "cubical_stokes")
    want = sys.argv[1] if len(sys.argv) > 1 else "sprint"
    papers = sorted(p for p in ROOT.glob("2026_*")
                    if (p / "main.tex").exists()
                    and (want == "all" or any(s in p.name for s in SPRINT)))
    if not papers:
        print("CONTROL FAILED: no papers found under", ROOT)
        return 2
    print(f"checking {len(papers)} papers under {ROOT}\n")
    bad = 0
    for p in papers:
        rows = check(p)
        flags = [r for r in rows if r[0] != "OK"]
        print(f"{p.name[5:]}")
        for tag, what, detail in rows:
            if tag != "OK":
                print(f"    {tag:9s} {what:22s} {detail}")
        if not flags:
            print(f"    all {len(rows)} checks OK")
        bad += len(flags)
    print(f"\n{bad} non-OK results across {len(papers)} papers")
    print("NOFIND means this script failed to look, not that the paper is missing something.")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
