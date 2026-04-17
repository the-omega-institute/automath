# Omega.Kronecker.W1DenominatorClosedForm

- File: `Omega/Kronecker/W1DenominatorClosedForm.lean`
- Struct: `KroneckerW1DenominatorClosedFormData`
- Paper label: `thm:kronecker-w1-denominator-closed-form`
- Goal theorem: `paper_kronecker_w1_denominator_closed_form`

## Structure docstring

Chapter-local wrapper for the denominator-length Kronecker `W₁` closed forms.
The data package the monotone-coupling quantile formula, the split on the sign of
`δ = α - p / q`, the bad-side linear evaluation together with its half-star-discrepancy
relation, and the good-side quadratic evaluation with constant star discrepancy.

## Goal

`D.badSideLinearClosedForm ∧ D.badSideHalfStarRelation ∧ D.goodSideQuadraticClosedForm ∧ D.goodSideStarConstant`

## Theorem docstring

Paper-facing wrapper for the denominator-length Kronecker `W₁` closed forms.
The monotone-coupling quantile identity and the split on `δ = α - p / q` recover the bad-side
linear formula and half-star-discrepancy relation, and likewise the good-side quadratic formula
and constant star discrepancy.
    thm:kronecker-w1-denominator-closed-form

## DAG

Nodes (Prop fields):
- `monotoneCouplingQuantileFormula` (leaf)
- `deltaSignSplit` (leaf)
- `badSideLinearClosedForm` (derived)
- `badSideHalfStarRelation` (derived)
- `goodSideQuadraticClosedForm` (derived)
- `goodSideStarConstant` (derived)

Edges:
- monotoneCouplingQuantileFormula + deltaSignSplit  →  **badSideLinearClosedForm**
- badSideLinearClosedForm  →  **badSideHalfStarRelation**
- monotoneCouplingQuantileFormula + deltaSignSplit  →  **goodSideQuadraticClosedForm**
- goodSideQuadraticClosedForm  →  **goodSideStarConstant**

## Imports
- `Mathlib.Tactic`
