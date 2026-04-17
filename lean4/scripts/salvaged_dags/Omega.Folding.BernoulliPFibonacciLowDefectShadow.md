# Omega.Folding.BernoulliPFibonacciLowDefectShadow

- File: `Omega/Folding/BernoulliPFibonacciLowDefectShadow.lean`
- Struct: `BernoulliPHalfLowDefectShadowData`
- Paper label: `thm:fold-bernoulli-p-fibonacci-low-defect-shadow`
- Goal theorem: `paper_fold_bernoulli_p_fibonacci_low_defect_shadow`

## Structure docstring

Chapter-local package for the Bernoulli-half low-defect Fibonacci shadow formulas.
The data record the closed form for the zero-defect coefficients together with the
derived one-defect and two-defect closed forms.

## Goal

`D.zeroDefectClosedForm ∧ D.oneDefectClosedForm ∧ D.twoDefectClosedForm`

## Theorem docstring

Paper-facing wrapper for the Bernoulli-half specialization of the order-four recurrence:
the low-defect coefficient sequences admit Fibonacci closed forms in defect orders
`0`, `1`, and `2`.
    thm:fold-bernoulli-p-fibonacci-low-defect-shadow

## DAG

Nodes (Prop fields):
- `zeroDefectClosedForm` (leaf)
- `oneDefectClosedForm` (derived)
- `twoDefectClosedForm` (derived)

Edges:
- zeroDefectClosedForm  →  **oneDefectClosedForm**
- zeroDefectClosedForm + oneDefectClosedForm  →  **twoDefectClosedForm**

## Imports
- `Mathlib.Tactic`
