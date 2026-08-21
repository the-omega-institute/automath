# Submission Checklist

Paper: `2026_zeckendorf_stable_arithmetic_fibonacci_congruence_online`
Title: `Zeckendorf Stable Arithmetic: Fibonacci Congruence, Field Phases, and Online Algorithms`
Authors: Haobo Ma; Wenlin Zhang
Target: Integers: Electronic Journal of Combinatorial Number Theory
Date: 2026-08-21

## Measurements

- [x] **Clean LaTeX builds**: PASS -- `latexmk -C main.tex` followed by `latexmk -pdfxe -interaction=nonstopmode -halt-on-error main.tex` completed successfully; the same cleared-state sequence with `latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex` also completed successfully.
- [x] **PDF page count**: PASS -- `pdfinfo` reports 34 pages for the clean XeLaTeX build (MiKTeX `xdvipdfmx`) and 34 pages for the clean pdfLaTeX build (MiKTeX `pdfTeX`).
- [x] **Authors rendered**: PASS -- `pdftotext -enc UTF-8 -f 1 -l 1 main.pdf -` prints `Haobo Ma` and `Wenlin Zhang` on the front page; the declared authors are Haobo Ma and Wenlin Zhang.
- [x] **MSC source declaration**: PASS -- copied from `main.tex` exactly: `Primary 11B39; Secondary 11A07, 11Y55, 68Q45.`
- [x] **Keywords**: PASS -- copied from `main.tex` exactly: `Zeckendorf representation; Fibonacci congruence; normal forms; finite automata; online addition; Fibonacci residue rings.`
- [x] **Abstract word count**: PASS -- `texcount -sum -brief -` run on the extracted `abstract` environment printed 163 words; the Integers: Electronic Journal of Combinatorial Number Theory author guidance states no numerical abstract word limit.
- [x] **Bibliography key sets**: PASS -- source scan measured 23 unique cited keys and 23 bibliography entries; missing keys: none; unused entries: none.
- [x] **Target journal record**: PASS -- `submission_metadata.md` names Integers: Electronic Journal of Combinatorial Number Theory as the primary target and `cover_letter_integers.txt` addresses that journal.

## Source integrity

- [x] **Source scope**: PASS -- no `main.tex` or section file was modified for this record.

## Content checks (restored)

These paper-specific items predate the measurement section above and are kept because
they record judgements no measurement makes: whether the cover letter leads with the
right theorem, whether related work is disclosed, whether the archival package is
complete. A checklist showing only mechanical PASSes reads clean while a known gap
is open.

| # | Item | Status |
| 1 | Cover letter leads with Theorem thm:mul-delay-linear-lower-bound and the bound delay >= n-1 | PASS |
| 2 | Companion manuscript ITA-2026-0032 and its relationship are disclosed in the cover letter | PASS |
| 3 | Online-adder section cites Labbe--Lepsova and the companion manuscript | PASS |
| 4 | Fenwick (2003) and Dimitrov--Donevsky (1995) are cited at the multiplication discussion | PASS |
| 5 | Novelty language is limited to the controlled index-search wording | PASS |
| 6 | Reproducibility statement names only artifacts/verify_multiplication_delay_bound.py after a successful run | PASS |
| 7 | Title, authors, affiliations, MSC codes, and keywords are present | PASS |
| 8 | Every bibliography entry is cited and every citation has a bibliography entry | PASS |
| 9 | No theorem statement or proof was altered | PASS |
| 10 | Editorial package contains no process notes or correction claims | PASS |
| 11 | latexmk compilation completes and produces main.pdf | PASS |
