# TRACK_BOARD -- Cubical Stokes Inverse / Boundary Readout

## Paper
Optimal Cubical Poincare--Stokes Inverses and Boundary Readout on Dyadic Approximations

## Target Journal
JDSGT / geometry-topology journal (to be determined after revision)

## Pipeline Status

| Stage | Status | Date |
|-------|--------|------|
| P2 Mathematical development | NEEDS REDO | -- |
| P3 Integration | -- | -- |
| P4 Editorial review | REJECT | 2026-04-04 |
| P5+ | blocked | -- |

## P4 Decision: REJECT -- return to P2

### Top 3 Blockers

1. **FATAL: Main theorem is false.** Theorem 3.1 bound $\|K_k\omega\|_\infty \le \frac{1}{2k}\|\omega\|_\infty$ has a concrete counterexample: $\omega = dx_1 \wedge dx_3 + dx_2 \wedge dx_3$ on $I^3$ gives $\|K_2\omega\|_\infty = 1/3 > 1/4$. Root cause: Lemma 2.1 contraction estimate is false for non-decomposable forms.

2. **Bibliography has 4 references.** Desk-reject level. Needs 15--20 minimum covering prior work on Poincare constants, Whitney forms, Cheeger constants, cubical cohomology, Minkowski dimension.

3. **Cheeger--Stokes duality (Prop 5.1) is tautological.** Assumes calibrating field exists, which is equivalent to the conclusion.

### Recommended Return Path

Return to P2. Three possible fix strategies:
- (A) Switch to comass norm where contraction estimate may hold
- (B) Restrict all theorems to decomposable forms
- (C) Find correct dimension-dependent constant for coefficient sup norm

Full review: `P4_EDITORIAL_REVIEW_2026-04-04.md`
