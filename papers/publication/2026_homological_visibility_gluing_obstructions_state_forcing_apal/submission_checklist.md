# Submission Checklist -- Cahiers

Paper: `Finite-Site Component Gerbes, Terminal Rigidity, and Prescribed Realization`
Target: Cahiers de Topologie et Geometrie Differentielle Categoriques
Date: 2026-08-17

---

## Structural checks

- [x] **Manuscript compiles (main.tex structure):** PASS
  - `main.tex` uses the `amsart` document class and inputs `sec_introduction.tex`, `sec_preliminaries.tex`, `sec_gerbe_obstruction.tex`, `sec_homological_visibility.tex`, `sec_homological_visibility_intrinsic.tex`, `sec_branch_aggregation.tex`, `sec_branch_contextuality.tex`, `sec_conclusion.tex`, and `sec_presentation_appendix.tex`; it uses `references.bib` via `unsrtnat`/`natbib`.
  - `supplement.tex` uses the `amsart` document class and inputs `sec_appendix.tex`.
  - All source targets exist in the submission directory. No circular or missing includes.
  - Local clean verification on 2026-08-17: `latexmk -pdfxe` completed successfully for both built documents. Current outputs: `main.pdf` (26 pages) and `supplement.pdf` (6 pages).

- [x] **All `\cite{}` keys match `references.bib` entries:** PASS
  - 17 unique cite keys are used across the built `.tex` sources. All 17 have corresponding entries in `references.bib`. No missing keys.

- [ ] **All `references.bib` entries are cited:** NOT MET
  - 17 of the 46 entries in `references.bib` are cited in the built documents; 29 entries are unused. This does not create undefined citations or add uncited entries to the generated bibliography.

- [x] **No files exceed 800-line limit:** PASS
  - `sec_homological_visibility.tex`: 545 lines (max)
  - `sec_gerbe_obstruction.tex`: 518 lines
  - `sec_appendix.tex`: 393 lines
  - `sec_preliminaries.tex`: 197 lines
  - `sec_branch_contextuality.tex`: 159 lines
  - `main.tex`: 152 lines
  - `sec_homological_visibility_intrinsic.tex`: 127 lines
  - `sec_branch_aggregation.tex`: 120 lines
  - `sec_introduction.tex`: 115 lines
  - `sec_presentation_appendix.tex`: 74 lines
  - `supplement.tex`: 52 lines
  - `sec_conclusion.tex`: 22 lines

- [x] **Abstract under 200 words:** PASS
  - Article English abstract: approximately 163 words. Supplement abstract: approximately 52 words.

- [x] **No revision-trace language:** PASS
  - No occurrences of prohibited phrases (revision notes, changelogs, "fixed," "updated version," etc.) in any submission `.tex` file. One use of "revisionary" in `sec_preliminaries.tex` is mathematical terminology ("cumulative rather than revisionary"), not editorial trace.

## Metadata checks

- [x] **Title-page author metadata present:** PASS
  - `main.tex` and `supplement.tex` list both authors, affiliations, and email addresses.

- [x] **Section numbering consistent:** PASS
  - Article Sections 1--8 are Introduction; The finite-site interface; Component gerbes and terminal rigidity; Finite good-cover sites and prescribed realization; Homological images and aggregate quotients; The wedge-of-spheres realization corollary; Boundary with empirical-model obstructions; and Conclusion. Appendix A is Naturality for specified presentation comparisons.
  - Supplement Appendices A--C are Presentation-comparison bookkeeping; Finite calculations; and A narrow lower-language separation example.

- [x] **Cross-references resolved (no `??` or dangling refs):** PASS
  - The clean XeLaTeX build logs contain zero undefined references and zero multiply-defined labels.

- [x] **MSC classification present:** PASS
  - `\subjclass[2020]{18F20, 18G50, 55N30}`

- [x] **Keywords present:** PASS
  - Article: finite sites; component gerbes; banded prestacks; good covers; homological images; universal coefficient theorem.
  - Supplement PDF metadata: finite sites; component gerbes; presentation comparison; homological images; finite abelian groups.

---

## Summary

| Check | Status |
|-------|--------|
| Manuscript structure | PASS |
| Cite-key validity | PASS (17/17 keys defined) |
| All bibliography database entries cited | NOT MET (17/46 cited) |
| Line limits | PASS (max 545) |
| Abstract length | PASS (~163 and ~52 words) |
| Revision-trace language | PASS |
| Author metadata | PASS |
| Section numbering | PASS |
| Cross-references | PASS |
| MSC classification | PASS |
| Keywords | PASS |

**Result: 10/11 PASS, 1 source-hygiene check not met (29 unused bibliography database entries).**

The two built documents compile without undefined citations or references. The unused database entries remain in `references.bib` but do not appear in the generated bibliographies.
