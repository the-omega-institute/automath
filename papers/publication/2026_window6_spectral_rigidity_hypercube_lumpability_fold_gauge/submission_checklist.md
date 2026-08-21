# Submission Checklist

Paper: `2026_window6_spectral_rigidity_hypercube_lumpability_fold_gauge`
Target: The Electronic Journal of Combinatorics
Date: 2026-08-20

## Checklist

- [x] **Manuscript text complete (no TODO/FIXME/XXX/HACK markers)**: PASS -- recursive scan of all 17 `.tex` files returns zero matches
- [x] **All figures/tables present**: PASS -- the built manuscript contains no `figure` or `table` environments; none are required by the source
- [x] **Bibliography key sets match**: PASS -- the built source recorded by `main.fls` cites 7 unique keys, exactly matching the 7 entries in `references.bib`; zero missing keys and zero unused entries
- [x] **Abstract word count and journal guidance checked**: CHECKED -- `texcount -sum -brief` reports 220 words for the extracted abstract; the EJC Author Guidelines retrieved on 2026-08-20 require an abstract but state no numerical word limit
- [x] **PDF page count**: PASS -- `pdfinfo` reports 9 pages for the clean-built `main.pdf` under `latexmk -pdfxe`. Engine-dependent: `latexmk -pdf` (pdfLaTeX) yields 10 pages from the same source, and no latexmkrc pins either engine.
- [x] **Clean LaTeX build**: PASS -- `latexmk -C main.tex` followed by `latexmk -pdfxe -interaction=nonstopmode -halt-on-error main.tex` completed with exit code 0
- [x] **Author information present**: PASS -- `main.tex` names Haobo Ma and Wenlin Zhang and supplies an affiliation and email address for each author
- [x] **MSC codes present**: PASS -- `main.tex` declares 2020 Mathematics Subject Classification codes 05C50 (primary), 11B39 and 11D61 (secondary)
- [x] **Keywords present**: PASS -- `main.tex` declares seven keywords: equitable partition, perfect colouring, hypercube, quotient spectrum, Zeckendorf representation, Fibonacci numbers, exponential Diophantine equation
- [x] **All cross-references resolve**: PASS -- the final clean-build log contains zero undefined-citation, undefined-reference, or multiply-defined-label warnings
- [x] **No change-tracking markup**: PASS -- recursive scan of all 17 `.tex` files finds zero change-tracking commands or a `changes` package declaration

## Summary

Ten items pass and one item is checked without a numerical journal limit. The manuscript declares MSC codes 05C50, 11B39, 11D61 and seven keywords beneath the abstract.
