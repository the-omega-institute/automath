# Omega.Folding.GaugeAnomalyQ10Tschirnhaus

- File: `Omega/Folding/GaugeAnomalyQ10Tschirnhaus.lean`
- Struct: `GaugeAnomalyQ10TschirnhausData`
- Paper label: `prop:fold-gauge-anomaly-Q10-tschirnhaus`
- Goal theorem: `paper_fold_gauge_anomaly_q10_tschirnhaus`

## Structure docstring

Chapter-local package for the explicit `Q10` Tschirnhaus elimination certificate. Besides the
already formalized `P10`/`Q10` inverse wrapper, the paper packages the resultant factorization,
the linear back-substitution, the branch-locus parametrization, and the precomputed
Galois/discriminant facts.

## Goal

`h.resultantFactorization ∧ h.linearBackSubstitution ∧ h.branchLocusParametrization ∧ h.galoisGroupS10 ∧ h.discriminantFactorization`

## Theorem docstring

Paper-facing wrapper for the `Q10` Tschirnhaus elimination package.
    prop:fold-gauge-anomaly-Q10-tschirnhaus

## DAG

Nodes (Prop fields):
- `resultantFactorization` (leaf)
- `linearBackSubstitution` (leaf)
- `branchLocusParametrization` (leaf)
- `galoisGroupS10` (leaf)
- `discriminantFactorization` (leaf)

Edges:
- (none)

## Imports
- `Mathlib.Tactic`
- `Omega.Folding.GaugeAnomalyP10Q10TschirnhausInverse`
