# Omega.Folding.GaugeAnomalyDensity

- File: `Omega/Folding/GaugeAnomalyDensity.lean`
- Struct: `FoldGaugeAnomalyDensityData`
- Paper label: `thm:fold-gauge-anomaly-density`
- Goal theorem: `paper_fold_gauge_anomaly_density`

## Structure docstring

Chapter-local wrapper for the limiting joint law of the gauge-anomaly bit pair `(X,Y)`. The
stored fields package the `4/9` mismatch density, the rational joint law, and the derived
marginals.

## Goal

`D.limitDensityIsFourNinths ∧ D.jointLawClosed ∧ D.derivedMarginalsClosed`

## Theorem docstring

Paper-facing wrapper for the uniform-baseline gauge-anomaly density theorem.
    thm:fold-gauge-anomaly-density

## DAG

Nodes (Prop fields):
- `limitDensityIsFourNinths` (leaf)
- `jointLawClosed` (leaf)
- `derivedMarginalsClosed` (leaf)

Edges:
- (none)

## Imports
- `Mathlib.Tactic`
- `Omega.Folding.GaugeAnomalyMean`
