# Submission Checklist

Paper: `2026_cubical_stokes_inverse_boundary_readout_jdsgt`
Target: Results in Mathematics
Date: 2026-08-20

## Checklist

- [x] **Manuscript text complete (no TODO/FIXME/XXX/HACK markers)**: PASS -- recursive scan of all 8 `.tex` files returns zero matches
- [x] **All figures/tables present**: PASS -- the built manuscript contains no `figure` or `table` environments; none are required by the source
- [ ] **Bibliography key sets match**: NOT MET -- 41 unique cited keys are all defined among 44 entries in `references_local.bib`; zero cited keys are missing, while 3 entries are unused: `Falconer2014`, `GueriniSavo2004`, and `Mattila1995`
- [ ] **Abstract word count against the target journal limit**: NOT CHECKED -- `texcount -sum -brief` reports 241 words for the extracted abstract, but the official submission-guidelines page returned a client challenge and no explicit Results in Mathematics numerical limit could be established from the manuscript package
- [x] **PDF page count**: PASS -- `pdfinfo` reports 28 pages for the clean-built `main.pdf`
- [x] **Clean LaTeX build**: PASS -- `latexmk -C main.tex` followed by `latexmk -pdfxe -interaction=nonstopmode -halt-on-error main.tex` completed with exit code 0
- [x] **Author information present**: PASS -- `main.tex` names Haobo Ma and Wenlin Zhang and supplies an affiliation and email address for each author
- [x] **MSC codes present**: PASS -- MSC 2020: 58A12, 35R30, 49Q20
- [x] **Keywords present**: PASS -- inverse problem; stability estimate; differential forms; homotopy operator; Whitney forms
- [x] **All cross-references resolve**: PASS -- source scan finds zero dangling reference targets, and the final clean-build log contains zero undefined-citation, undefined-reference, or multiply-defined-label warnings
- [x] **No change-tracking markup**: PASS -- recursive scan of all 8 `.tex` files finds zero change-tracking commands or a `changes` package declaration

## Summary

Nine items pass. The bibliography database has three unused entries, and the abstract-limit comparison is not checked because no explicit journal limit was established.
