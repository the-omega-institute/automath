# Submission Checklist -- APAL

Paper: `Homological Visibility of Gluing Obstructions in a State-Forcing Semantics`
Target: Annals of Pure and Applied Logic
Date: 2026-03-30

---

## Structural checks

- [x] **Manuscript compiles (main.tex structure):** PASS
  - `main.tex` uses `amsart` document class, inputs 9 section files plus appendix, bibliography via `plainnat`/`natbib`. All `\input{}` targets exist in the submission directory. No circular or missing includes.
  - Local verification on 2026-03-30: `pdflatex -> bibtex -> pdflatex -> pdflatex` completed successfully. Current output: `main.pdf` (37 pages).

- [x] **All `\cite{}` keys match `references.bib` entries:** PASS
  - 15 unique cite keys used across all `.tex` files. All 15 have corresponding entries in `references.bib`. No missing keys.

- [x] **All `references.bib` entries are cited:** PASS
  - 15 entries in `references.bib`, all 15 cited in at least one `.tex` file. Zero orphan entries.

- [x] **No files exceed 800-line limit:** PASS
  - `sec_null_decomposition.tex`: 580 lines (max)
  - `sec_branch_aggregation.tex`: 572 lines
  - `sec_homological_visibility.tex`: 571 lines
  - `sec_gerbe_obstruction.tex`: 479 lines
  - `sec_multiaxis_refinement.tex`: 260 lines
  - `sec_information_states.tex`: 121 lines
  - `sec_preliminaries.tex`: 100 lines
  - `main.tex`: 87 lines
  - `sec_introduction.tex`: 43 lines
  - `sec_appendix.tex`: 29 lines
  - `sec_conclusion.tex`: 23 lines

- [x] **Abstract under 200 words:** PASS
  - Approximately 161 words.

- [x] **Sequel files NOT in submission directory:** PASS
  - `sec_observer_spacetime.tex` and `sec_conservativity.tex` are in `sequel/` subdirectory only. Neither appears in `main.tex`.

- [x] **No revision-trace language:** PASS
  - No occurrences of prohibited phrases (revision notes, changelogs, "fixed," "updated version," etc.) in any submission `.tex` file. One use of "revisionary" in `sec_preliminaries.tex` is mathematical terminology ("cumulative rather than revisionary"), not editorial trace.

## Metadata checks

- [ ] **Title-page author metadata present:** BLOCKER
  - `main.tex` line 59 still has `\author{}` with no names, affiliations, or corresponding-author details.
  - APAL Guide for Authors checked on 2026-03-30 states that the journal uses single anonymized review and requires all authors to be listed in the manuscript and entered in the submission system.
  - Before upload, insert the definitive author list and corresponding-author metadata on the title page.

- [x] **Section numbering consistent:** PASS
  - Sections 1--6 plus Appendix. Section 1 (Introduction), Section 2 (Preliminaries), Section 3 (Information States), Section 4 (Local Objects -- spans `sec_null_decomposition.tex`, `sec_gerbe_obstruction.tex`, `sec_homological_visibility.tex`, `sec_branch_aggregation.tex` via subsections), Section 5 (Refinement Dynamics), Section 6 (Conclusion), Appendix (Complexity). Introduction roadmap matches actual structure.

- [x] **Cross-references resolved (no `??` or dangling refs):** PASS
  - No `??` tokens found in any `.tex` file. P4 review confirmed 0 dangling references.

- [x] **MSC classification present:** PASS
  - `\subjclass[2020]{03B45, 03F55, 03G30, 18F20}`
  - 03B45 (Algebraic logic), 03F55 (Intuitionistic mathematics), 03G30 (Categorical logic, topoi), 18F20 (Presheaves and sheaves, cohomology).

- [x] **Keywords present:** PASS
  - `\keywords{state forcing, local objects, sheafification, gerbes, visible quotient, universal coefficient theorem}`

---

## Summary

| Check | Status |
|-------|--------|
| Manuscript structure | PASS |
| Cite/bib consistency | PASS (15/15 both directions) |
| Line limits | PASS (max 580) |
| Abstract length | PASS (~161 words) |
| Sequel separation | PASS |
| Revision-trace language | PASS |
| Author field | BLOCKER (missing title-page author metadata) |
| Section numbering | PASS |
| Cross-references | PASS |
| MSC classification | PASS |
| Keywords | PASS |

**Result: 11/12 PASS, 1 blocker (title-page author metadata missing).**

The submission pack is internally verified, but not ready for upload until manuscript author metadata is supplied.
