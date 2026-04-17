# Omega.Folding.GaugeAnomalyPSDRational

- File: `Omega/Folding/GaugeAnomalyPSDRational.lean`
- Struct: `GaugeAnomalyPSDRationalData`
- Paper label: `thm:fold-gauge-anomaly-psd-rational`
- Goal theorem: `paper_fold_gauge_anomaly_psd_rational`

## Structure docstring

Chapter-local wrapper for the rational power-spectrum formula of the gauge anomaly. The
fields record the closed covariance generating function, the value of `C₀`, the substitution of
`s` and `s⁻¹` into the two-sided covariance sum, the denominator-clearing step, and the final
rational/closed-form readout.

## Goal

`D.psdIsRational ∧ D.psdClosedForm`

## Theorem docstring

Paper-facing wrapper for the rational closed form of the gauge-anomaly power spectral density.
    thm:fold-gauge-anomaly-psd-rational

## DAG

Nodes (Prop fields):
- `covarianceGeneratingFunctionClosed` (leaf)
- `covarianceZeroClosed` (leaf)
- `substitutedLaurentSum` (derived)
- `denominatorsCleared` (derived)
- `psdIsRational` (derived)
- `psdClosedForm` (derived)

Edges:
- covarianceGeneratingFunctionClosed + covarianceZeroClosed  →  **substitutedLaurentSum**
- substitutedLaurentSum  →  **denominatorsCleared**
- denominatorsCleared  →  **psdIsRational**
- denominatorsCleared  →  **psdClosedForm**

## Imports
- `Mathlib.Tactic`
- `Omega.Folding.GaugeAnomalyCovarianceRecurrenceIntegersHankelRank3`
- `Omega.Folding.GaugeAnomalyTauIntClosed`
