# Stage-1 verification artifact for arXiv:2601.07933

This directory contains a Stage-1 computational artifact for the line of work in:

> Daniel Litt, Ruochuan Liu Lam. p-curvature and non-abelian cohomology. arXiv:2601.07933, January 2026.

The target result is Theorem 6.1.1 in the relative-curve setting. In plain English, the theorem says that for a smooth family of curves, if the p-curvature of the isomonodromy foliation vanishes, then the family is forced to be isotrivial: after a suitable base change, the curve is not really varying.

The proof structure uses three major ingredients:

- Chen's formula for p-curvature in the isomonodromy setting.
- Surjectivity of the Hitchin map onto `H^0(C, K_C^2)`.
- The perfect Serre-duality pairing that turns a nonzero Kodaira-Spencer direction into a detectable obstruction.

## Stage-1 Scope

The checker `check_2601_07933_genus2_serre_pairing_stage1.py` certifies only a small linear-algebra skeleton for a concrete genus-2 hyperelliptic curve:

```text
C: y^2 = x (x - 1) (x - 2) (x - 3) (x - 4) (x - 5).
```

It verifies, with exact Sympy rational arithmetic, that this degree-6 model has six distinct rational branch points and genus `g = 2`. It records the standard genus-2 hyperelliptic basis

```text
H^0(K_C) = span{ dx/y, x dx/y }
```

and the standard quadratic-differential basis

```text
H^0(K_C^2) = span{ (dx/y)^2, x (dx/y)^2, x^2 (dx/y)^2 }.
```

For the pairing check, the script builds the explicitly requested `3 x 3` exact-arithmetic matrix

```text
M_ij = sum_{k=0..5} x_k^(i+j) / f'(x_k),    i,j in {0,1,2},
```

where `x_k` runs over the six roots of `f`. The JSON labels this form as `INTERSECTION_PROXY`: it is the `f'(x_k)`-weighted Frobenius-style symmetric bilinear form on `H^0(K_C^2)`, intended as a rank-detection proxy from residues/intersections, not the genuine Serre cup product.

The script also records the elementary Hitchin sanity check that for a rank-2 Higgs bundle, `det(phi)` lands in `H^0(K_C^2)`, whose target dimension is `3` in this example.

## What Stage 1 Does Not Do

This artifact is intentionally narrow. It does not construct an isomonodromy lift, compute p-curvature, prove Chen's formula, or verify global surjectivity of the Hitchin map. It also does not compute the genuine Serre cup product. It certifies only the pointwise genus-2 linear-algebra bookkeeping and the requested exact `INTERSECTION_PROXY` matrix for the chosen curve.

Run:

```text
python3 tools/community-outreach/targets/litt_pcurvature_followup/check_2601_07933_genus2_serre_pairing_stage1.py
```

The generated JSON output is:

```text
tools/community-outreach/targets/litt_pcurvature_followup/check_2601_07933_genus2_serre_pairing_stage1_output.json
```
