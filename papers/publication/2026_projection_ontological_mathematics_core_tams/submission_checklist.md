# Submission Checklist

Paper: `2026_projection_ontological_mathematics_core_tams`
Title: `Finite-Window Zeckendorf Fibers and the Discrete Thermodynamics of Fibonacci Partition Differences`
Authors: Haobo Ma; Wenlin Zhang
Target: Journal of Number Theory
Date: 2026-08-21

## Measurements

- [x] **Clean LaTeX builds**: PASS -- `latexmk -C main.tex` followed by `latexmk -pdfxe -interaction=nonstopmode -halt-on-error main.tex` completed successfully; the same cleared-state sequence with `latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex` also completed successfully.
- [x] **PDF page count**: PASS -- `pdfinfo` reports 50 pages for the clean XeLaTeX build (MiKTeX `xdvipdfmx`) and 50 pages for the clean pdfLaTeX build (MiKTeX `pdfTeX`).
- [x] **Authors rendered**: PASS -- `pdftotext -enc UTF-8 -f 1 -l 1 main.pdf -` prints `HAOBO MA AND WENLIN ZHANG` on the front page; the declared authors are Haobo Ma and Wenlin Zhang.
- [x] **MSC 2020**: PASS -- copied from `main.tex` exactly: `11B39, 11R32, 68Q45, 94A17`.
- [x] **Keywords**: PASS -- copied from `main.tex` exactly: `Zeckendorf representation, Fibonacci partition function, collision moments, discrete thermodynamics, pressure, Galois groups, Chebotarev density`.
- [x] **Abstract word count**: PASS -- `texcount -sum -brief -` run on the extracted `abstract` environment printed 330 words; the Journal of Number Theory author guidance states no numerical abstract word limit.
- [x] **Bibliography key sets**: PASS -- source scan measured 19 unique cited keys and 19 bibliography entries; missing keys: none; unused entries: none.
- [x] **Target journal record**: PASS -- `submission_metadata.md` names Journal of Number Theory as the primary target and `cover_letter_jnt.txt` addresses that journal.

## Source integrity

- [x] **Source scope**: PASS -- no `main.tex` or section file was modified for this record.

## Content checks (restored)

These paper-specific items predate the measurement section above and are kept because
they record judgements no measurement makes: whether the cover letter leads with the
right theorem, whether related work is disclosed, whether the archival package is
complete. A checklist showing only mechanical PASSes reads clean while a known gap
is open.

| # | Item | Status |
| 1 | Title page complete (title, author, address, date, thanks) | PASS |
| 2 | Abstract present and at most 250 words | PASS |
| 3 | MSC 2020 codes declared (11B39, 11R32, 68Q45, 94A17) | PASS |
| 4 | Keywords declared | PASS |
| 5 | All theorems/propositions/lemmas/corollaries numbered | PASS |
| 6 | All proofs complete (no "proof omitted" or placeholders) | PASS |
| 7 | Bibliography: every entry cited in text, every citation in bibliography | PASS |
| 8 | No undefined references or dangling labels | PASS |
| 9 | No revision-trace language (no "new", "revised", "fixed", "updated") | PASS |
| 10 | Every .tex file under 800 lines (max: sec_moment_kernel at 682) | PASS |
| 11 | Author and affiliation present (\author, \address, \thanks) | PASS |
| 12 | LaTeX compiles clean with amsart documentclass | PASS |
| 13 | Complete archival package for the q=9,...,17 computation | INCOMPLETE: see `artifacts/README.md` |
