# Submission Checklist

Paper: `2026_scan_projection_address_semantics_sigma_nonexpansion_etds`  
Target journal: Stochastics and Dynamics  
Measured: 2026-08-21

## Checklist

- [x] **Target journal identified**: PASS -- `submission_metadata.md` names Stochastics and Dynamics, and `cover_letter_stochastics_and_dynamics.txt` is addressed to Stochastics and Dynamics. No ETDS requirement is used.
- [x] **Manuscript marker scan**: PASS -- across all `.tex` files, searches for `TODO`, `FIXME`, `XXX`, and `HACK` return zero matches.
- [x] **Figures and tables**: PASS -- the source contains 0 `figure` environments and 0 `table` environments.
- [ ] **Abstract length rule**: MEASURED -- the rendered PDF abstract contains 219 words. The Stochastics and Dynamics abstract limit was not verified from the available paper files.
- [ ] **Page-limit rule**: MEASURED -- `main.log` reports an 18-page XeTeX output, and `main.aux` records `\@abspage@last{18}`. The Stochastics and Dynamics page limit was not verified from the available paper files.
- [x] **Appendix scan**: PASS -- the source contains 0 `appendix` environments.
- [x] **Author information**: PASS -- `main.tex` declares Haobo Ma and Wenlin Zhang with affiliations and email addresses; page 1 of `main.pdf` renders both names and both contact blocks.
- [x] **MSC codes**: PASS -- `main.tex` and page 1 of `main.pdf` show 37A50, 37B10, 60F05, and 60J10.
- [x] **Keywords**: PASS -- the source contains 5 keywords: open symbolic dynamics; periodic Markov chains; R'enyi pressures; collision processes; Poisson approximation.
- [ ] **Bibliography accounting**: REVIEW -- `main.tex` embeds 26 `\bibitem` entries and has no `\bibliography` command. The manuscript contains 12 distinct cited keys and 14 uncited entries that still print in `thebibliography`; `references.bib` is not part of the active build.
- [x] **Cross-reference resolution**: PASS -- there are 49 distinct `\ref`/`\eqref` targets across the `.tex` sources, with 0 targets lacking a matching `\label`.

## Summary

9 measured checks pass. 3 items require an external journal-rule check or an editorial decision: abstract length, page limit, and the 14 uncited printed bibliography entries.
