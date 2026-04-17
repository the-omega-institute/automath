# Omega.EA.PrimeRegisterEllipseInvertGodel

- File: `Omega/EA/PrimeRegisterEllipseInvertGodel.lean`
- Struct: `PrimeRegisterEllipseInvertGodelData`
- Paper label: `thm:prime-register-ellipse-invert-godel`
- Goal theorem: `paper_prime_register_ellipse_invert_godel`

## Structure docstring

Chapter-local wrapper for recovering the prime-register scale from Joukowsky ellipse data.
The inputs record the axis-based and second-moment-based readouts together with the residual-ledger
uniqueness package, and the outputs are the three paper-facing consequences.

## Goal

`D.scaleRecoveredFromAxes ∧ D.scaleRecoveredFromSecondMoment ∧ D.rationalScaleRecoversPrimeExponentVector`

## Theorem docstring

Paper-facing wrapper: either the semi-axes or the second radial moment recovers the same
scale, and the rational-scale uniqueness package recovers the prime exponent vector.
    thm:prime-register-ellipse-invert-godel

## DAG

Nodes (Prop fields):
- `axesDetermineScale` (leaf)
- `secondMomentDeterminesScale` (leaf)
- `rationalScaleUniqueness` (leaf)
- `scaleRecoveredFromAxes` (leaf)
- `scaleRecoveredFromSecondMoment` (leaf)
- `rationalScaleRecoversPrimeExponentVector` (leaf)

Edges:
- (none)

## Imports
- `Mathlib.Tactic`
- `Omega.EA.JoukowskyEllipse`
- `Omega.EA.PrimeRegisterResidualLedgerGroup`
