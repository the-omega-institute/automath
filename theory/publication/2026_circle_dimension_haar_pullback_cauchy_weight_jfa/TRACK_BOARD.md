# TRACK_BOARD -- Publication Pipeline Status

Paper: *Cayley--Chebyshev Mode Calculus, Poisson Entropy Asymptotics, and Cardinal Reconstruction in a Strip RKHS*
Target: Journal of Functional Analysis (JFA)
Directory: `theory/publication/2026_circle_dimension_haar_pullback_cauchy_weight_jfa/`

---

## Pipeline Stages

| Stage | Name | Status | Date | Notes |
|---|---|---|---|---|
| **P0** | Extraction & Scope | DONE | 2026-03-30 | Extracted from parent theory; scope defined in README.md; single mainline: Cayley -> Haar -> cdim -> Poisson -> RKHS -> lattice |
| **P1** | Traceability | DONE | 2026-03-30 | SOURCE_MAP.md created (37 claims mapped to parent sources + Lean status); THEOREM_LIST.md created (38 claims, all PROVED) |
| **P2** | Research Extension | DONE | 2026-03-30 | P2_EXTENSION_NOTE_2026-03-30.md created; 4 theorem packages identified; 5 gaps analyzed; sharpened lineup proposed |
| **P3** | Lean Linkage & Audit | PENDING | -- | Circle dimension: 1 partial Lean match (CircleDim.lean, simplified model). Analytic content: 0 Lean coverage. Full linkage audit deferred until algebraic claims formalized in mathlib style. |
| **P4** | Journal-Fit Check | PENDING | -- | Preliminary assessment: JFA-appropriate. MSC codes set (47D07, 94A17, 46E22, 42C15, 30H10). Page count ~40pp, within JFA range. Formal fit-check after P5 completion. |
| **P5** | Proof Polish | PENDING | -- | All proofs present. Action items: (1) optimality of $W_2$ exponent (Gap 1); (2) bridging paragraph algebraic->analytic (Gap E1); (3) $K = \pi P_2$ highlight (Gap E2). |
| **P6** | LaTeX Build & Bib | PENDING | -- | review_notes.txt indicates prior build succeeded conceptually. Need clean pdflatex/bibtex cycle in live environment. References pruned to 23 entries (references.bib). |
| **P7** | Submission | PENDING | -- | Target: JFA first submission. Fallback: Annales de l'Institut Fourier. |

---

## Blocking Issues

| ID | Description | Blocks | Priority |
|---|---|---|---|
| B1 | $W_2$ exponent optimality (Gap 1 from P2) | P5 | Medium -- strengthens T13 but not strictly required |
| B2 | Clean LaTeX build verification | P6, P7 | High -- must compile before submission |
| B3 | Circle dimension algebra conciseness | P4 | Low -- referee may request compression |

---

## File Inventory

| File | Lines | Role | Status |
|---|---|---|---|
| `main.tex` | 112 | Document shell | Complete |
| `sec_introduction.tex` | 144 | Introduction + roadmap | Complete |
| `sec_preliminaries.tex` | 53 | Notation | Complete |
| `sec_cayley_gate.tex` | 46 | Cayley transform | Complete |
| `sec_haar_pullback.tex` | 88 | Haar pullback rigidity | Complete |
| `sec_circle_dimension_algebra.tex` | 447 | Circle dimension + phase sampling | Complete |
| `sec_precision_potential.tex` | ~1687 | Entropy, modes, RKHS, lattice, reconstruction | Complete (largest section) |
| `sec_appendix.tex` | 84 | Trigonometric integrals | Complete |
| `references.bib` | 265 | Bibliography (23 entries) | Complete |
| `review_notes.txt` | 21 | Referee simulation notes | Reference |
| `README.md` | 109 | Paper scope + extraction record | Complete |
| `SOURCE_MAP.md` | -- | Traceability map | Created 2026-03-30 |
| `THEOREM_LIST.md` | -- | All claims + proof status | Created 2026-03-30 |
| `P2_EXTENSION_NOTE_2026-03-30.md` | -- | Extension analysis | Created 2026-03-30 |
| `TRACK_BOARD.md` | -- | This file | Created 2026-03-30 |

---

## sec_precision_potential.tex Length Warning

At ~1687 lines, `sec_precision_potential.tex` exceeds the 800-line project limit (CLAUDE.md). Recommended split:

1. `sec_entropy_asymptotics.tex` (~600 lines): Subsections 5.1--5.5 (entropy identity through defect stability)
2. `sec_rkhs_reconstruction.tex` (~600 lines): Subsections 5.6--5.9 (Gram kernel through cardinal reconstruction)
3. `sec_poisson_data.tex` (~300 lines): Subsections 5.7 centered reconstruction + channel RKHS
4. Alternatively, a two-way split along the natural break at subsection 5.6 (the mode Gram kernel)

**This split is a P5 action item.** The mathematical content is complete; only the file organization needs adjustment.

---

## Next Actions

1. **P5-1:** Split `sec_precision_potential.tex` into two files at the RKHS boundary
2. **P5-2:** Add optimality paragraph for $W_2$ exponent (Gap 1)
3. **P5-3:** Add bridging paragraph at the algebraic-analytic transition (Gap E1)
4. **P5-4:** Highlight $K = \pi P_2$ in RKHS subsection (Gap E2)
5. **P6-1:** Run clean LaTeX build cycle
6. **P4-1:** Final journal-fit assessment after P5 completion
