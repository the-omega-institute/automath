# Pipeline: Cayley-Chebyshev Mode Calculus / Poisson Entropy / Strip RKHS (JFA)
Target: Journal of Functional Analysis (JFA)
Status: P4 complete, P5--P7 pending

## Stage Progress

| Stage | Status | Date | Notes |
|---|---|---|---|
| P0 Extraction and Scope | completed | 2026-03-30 | Single mainline: Cayley -> Haar -> cdim -> Poisson -> RKHS -> lattice |
| P1 Traceability | completed | 2026-03-30 | 37 claims mapped; all PROVED |
| P2 Research Extension | completed | 2026-03-30 | 4 theorem packages; 5 gaps analyzed; sharpened lineup proposed |
| P3 Lean Linkage | completed | 2026-03-30 | 1 partial Lean match (CircleDim.lean). Analytic content: 0 coverage |
| P4 Journal-Fit Check | completed | 2026-03-30 | Abstract rewritten; sec_precision_potential split into 3 files; intro roadmap updated; 3 orphan bib entries removed; sec_circle_dimension_algebra.tex excluded (algebraic, not JFA scope); \cdim macro removed; revision-trace language cleaned; 24 bib entries remain, all cited |
| P5 Proof Polish | pending | -- | Action items: W2 exponent optimality, algebraic->analytic bridge, K=piP2 highlight |
| P6 LaTeX Build | pending | -- | All .tex files under 800 lines. Clean build verification needed |
| P7 Submission | pending | -- | Target: JFA. Fallback: Annales de l'Institut Fourier |

### Blocking Issues

- Clean LaTeX build verification needed

## Theorem Inventory

### Headline results (38 claims total, all proved)

| Package | Key results | Description |
|---|---|---|
| A: Cayley-Chebyshev Mode Calculus | T8 `thm:cayley-chebyshev-mode`, P9, C2 | Mode expansion via Chebyshev polynomials; finite Fourier formulas |
| B: Entropy Asymptotics / Defect | T9--T13 | Even-order vanishing (T9), eighth-order KL formula (T10), defect ladder (T11), defect amplification $\Delta_8 \ge (13\sigma^2/8)\Delta_6$ (T12), $W_2$-stability (T13) |
| C: RKHS / Operator | T14--T19 | Gram kernel $K(a,b)=2/(4+(a-b)^2)$ (T14), mode-space spanning (T15), Poisson image realization (P10), Hardy splitting (P11), lattice Riesz bounds (T18), cardinal reconstruction (T19) |
| D: Reconstruction | T16, T17, C3, C4 | Central Poisson trace determines centred law; RKHS evaluation functionals |

### Supporting results

- T1 `thm:haar-pullback-uniqueness`: Cayley is unique chart pulling Haar to Cauchy
- T2--T6 (circle dimension): Excluded from JFA paper (algebraic, retained in sec_circle_dimension_algebra.tex)

## Source Map

- Parent: `theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/sections/body/circle_dimension_phase_gate/`
- `sec_introduction.tex`: Introduction and roadmap
- `sec_preliminaries.tex`: Notation and conventions
- `sec_cayley_gate.tex` (46 lines): Cayley transform
- `sec_haar_pullback.tex` (88 lines): Haar pullback rigidity
- `sec_entropy_asymptotics.tex`: Entropy identity, mode calculus, KL asymptotics, defect, stability
- `sec_gram_space.tex`: Mode Gram kernel, RKHS, centered reconstruction
- `sec_strip_lattice.tex`: Strip RKHS, Hardy splitting, lattice sampling, cardinal reconstruction
- `sec_appendix.tex` (84 lines): Trigonometric integrals
- `sec_circle_dimension_algebra.tex` (447 lines): Circle dimension + phase sampling (NOT included in main.tex -- algebraic content outside JFA scope; candidate for deletion or separate publication)

## Stage Notes

### P2 Research Extension

Four interlocking theorem packages identified, each at JFA level. The mode calculus (Package A) drives the parity structure forcing even-order vanishing in the entropy expansion. The defect amplification $\Delta_8 \ge (13\sigma^2/8)\Delta_6$ (Package B) is a genuinely new higher-order rigidity phenomenon. The RKHS package (C) provides a Poisson/Cauchy analogue of Gaussian lattice theory with explicit lattice symbols and cardinal kernels.

**Gaps identified:**
1. W2 exponent sharpness: T13 gives $O(\Delta_6^{1/4})$ but no matching lower bound (low-medium difficulty)
2. Extension to general f-divergences (medium difficulty)
3. Non-lattice sampling extension (low difficulty)
4. Higher-dimensional Poisson kernels (high difficulty, deferred)
5. Lean formalization (not a submission requirement)
E1. Bridging paragraph: algebraic section -> analytic section transition
E2. Highlight $K = \pi P_2$ in RKHS subsection

**Competing literature:** Romero-Ulanovskii-Zlotnikov (JFA 2024, Gaussian shift-invariant spaces), Baranov-Belov-Grochenig (ACHA 2022, Gaussian lattice interpolation), Bobkov-Chistyakov-Gotze (entropic CLT -- fundamentally different setting).

**Lean coverage:** 1 partial match (circleDim simplified model). All functional-analytic content outside current Lean scope.
