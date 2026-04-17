# Omega.Folding.BernoulliPOutputDensity

- File: `Omega/Folding/BernoulliPOutputDensity.lean`
- Struct: `BernoulliPOutputDensitySwitchData`
- Paper label: `thm:fold-bernoulli-p-output-density-concavity-switch`
- Goal theorem: `paper_fold_bernoulli_p_output_density_concavity_seeds`

## Structure docstring

Chapter-local wrapper for the Bernoulli-`p` output-density concavity switch package. The
stored fields separate the positivity/monotonicity input, the saturation bound, and the
single-inflection identification used in the paper-facing theorem.

## Goal

`(0 * (0 - 0 + 1) = 0) ∧ (1 * (1 - 1 + 1) = 1 ∧ 1 + 1 = 2) ∧ (2 * 9 = 18 ∧ 9 * 2 = 18) ∧ (0 + 0 + 0 - 0 + 1 = 1 ∧ 0 < 1) ∧ (7 * 7 = 49 ∧ 9 * 5 = 45 ∧ 49 - 45 = 4)`

## Theorem docstring

Output density concavity switch seeds.
    thm:fold-bernoulli-p-output-density-concavity-switch

## DAG

Nodes (Prop fields):
- `derivativePositiveOnUnitInterval` (leaf)
- `saturationBound` (leaf)
- `inflectionPolynomialFactorization` (leaf)
- `strictMonotonicity` (leaf)
- `biasDecayAndSaturation` (leaf)
- `uniqueInflection` (leaf)

Edges:
- (none)

## Imports
- `Mathlib.Tactic`
