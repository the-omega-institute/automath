# Submission Checklist

Paper: `2026_scan_projection_address_semantics_sigma_nonexpansion_etds`
Target: Ergodic Theory and Dynamical Systems (ETDS)
Date: 2026-03-30

## Checklist

- [x] **Manuscript text complete (no TODO/FIXME markers)**: PASS -- grep for TODO, FIXME, XXX, HACK across all .tex files returns zero matches
- [x] **All figures/tables present**: PASS -- manuscript contains no figures or tables; none are referenced
- [x] **Bibliography complete (no missing keys)**: PASS -- 17 cited keys exactly match 17 entries in `references.bib`; zero unused entries, zero missing entries
- [x] **Abstract word count**: PASS -- approximately 141 words; ETDS limit is ~200 words
- [x] **Page count estimate**: PASS -- approximately 35 pages at 12pt a4paper with 2.7cm margins (3196 source lines across 8 section files + main.tex); within ETDS norms for a research article
- [x] **Appendix proportion**: PASS -- manuscript has no appendices; all material is in the main body
- [ ] **Author information present**: FAIL -- `\author{}` in main.tex is empty; author names and affiliations must be added before submission
- [x] **MSC codes present**: PASS -- MSC 2020: 37B10, 37A50, 37D35, 94A17
- [x] **Keywords present**: PASS -- open symbolic dynamics, escape rates, Ruelle resonances, Renyi pressures, Poisson approximation, hidden conditional entropy
- [x] **No revision metadata in manuscript**: PASS -- no revision traces, change logs, or draft-stage language found in any .tex file
- [x] **All cross-references resolve**: PASS -- 27 distinct `\ref{}` targets all have corresponding `\label{}` definitions; zero dangling references
- [x] **Formalization status noted**: PASS -- documented in `LEAN_SYNC_NOTE_2026-03-30.md`: 0% verified, 27% partial (4 of 15 active claims have partial Lean 4 support); non-blocking for submission

## Summary

11 of 12 items pass. One blocker:

1. **Author field is empty** -- author names, affiliations, and contact information must be inserted into `main.tex` before the submission can proceed.

## Notes

- BIB_SCOPE previously noted 5 unused entries; these were already removed in the P5 integration pass. Current bibliography is clean.
- P3 flagged three deferred editorial decisions (title length, Sturmian section placement, hidden-entropy subsection). These remain deferred to referee feedback.
- The Lean formalization coverage is low but this is standard for a first submission; the LEAN_SYNC_NOTE documents exact coverage for future work.
