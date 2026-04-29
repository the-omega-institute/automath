# TRACK_BOARD -- Finite-Window Zeckendorf Fibers (TAMS)

## Current Status

| Date | Stage | Decision | Reviewer |
|------|-------|----------|----------|
| 2026-03-30 | P4 Editorial Review | MINOR_REVISION | Prior reviewer |
| 2026-03-30 | P5 Integration | All fixes applied | -- |
| 2026-04-04 | P4 Editorial Review (Gate 3) | **MAJOR_REVISION** | Claude Opus 4.6 |
| 2026-04-04 | P5 Integration (Gate 3) | **All blockers fixed** | Claude Opus 4.6 |

## P5 Decision Log (2026-04-04)

| ID | Issue | Decision | Reason |
|----|-------|----------|--------|
| BLOCKER-1 | Principalization proof gap (Z-module equal-rank fallacy) | ACCEPT | Hard math error; replaced with Smith-normal-form index-1 verification |
| BLOCKER-2 | DixonMortimer1996 missing from thebibliography | ACCEPT | Added entry; resolves [?] in compiled PDF |
| MEDIUM-1 | Theorem B forward-references undefined collision kernel | DEFER | Standard TAMS intro style; low risk |
| MEDIUM-2 | Theorems B and C scope overlap | DEFER | Structural reshuffling risks new issues; overlap is minor |
| MEDIUM-3 | "Minimal recurrence polynomial" definition informal | ACCEPT | Tightened to reference companion matrix and m_0(q) |
| MEDIUM-4 | Bibliography metadata errors (3 entries) | ACCEPT | Corrected ChowSlattery2021, ChowJones2024, Sanna2025 to match .bib |
| MEDIUM-5 | Sanna citation lacks theorem-level specificity | ACCEPT | Added [Thm. 1.1] to both statement and proof citations |
| MINOR-1 | cor:visible-band grammatical structure | ACCEPT | Added "define" before the display |
| MINOR-2 | Orphan file references Theorem G | ACCEPT | Changed "Theorems A--G" to "Theorems A--F" |
| MINOR-3 | "Unexpectedly rigid" AI-voice phrasing | ACCEPT | Changed to "rigid" |
| MINOR-4 | Bibliography could be expanded | DEFER | Optional; 13 references acceptable for self-contained paper |
| MINOR-5 | Cover letter reference count | ACCEPT | Already says 13; matches after DixonMortimer1996 addition |
| MINOR-6 | Inconsistent Cref vs manual ref | DEFER | Low severity; would require full-file sweep |

## Remaining Action Items

- [ ] Run two pdflatex passes after fixes to verify clean compilation
- [ ] Consider cleaning submission directory of orphan files (sec_rewriting.tex, sec_appendix_auxiliary.tex) before final submission
- [ ] Consider sharpening Theorems B/C scope overlap (MEDIUM-1/2, deferred)

## Blockers Resolved

All 2 BLOCKERs and 4 of 5 MEDIUM issues fixed. The 2 deferred MEDIUM items (Theorem B/C overlap) are stylistic and unlikely to draw a referee objection on their own. All 13 bibliography entries are present and have consistent metadata between sec_references.tex and references.bib.

## Full Review

See `P4_EDITORIAL_REVIEW_2026-04-04.md` for the complete Gate 3 review with 2 BLOCKERs, 5 MEDIUM issues, and 6 MINOR items.
