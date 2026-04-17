# Omega.Experiments.KLFromTVQmin

- File: `Omega/Experiments/KLFromTVQmin.lean`
- Struct: `KLFromTVQminData`
- Paper label: `?`
- Goal theorem: `paper_kl_from_tv_qmin`

## Structure docstring

Chapter-local package for the standard KL-from-TV estimate under a positive minimum `q`-atom.
The data records the shared-support / minimum-atom hypotheses, the intermediate
`χ²`-bound extracted from the `ℓ¹` distance, the logarithmic KL-vs-`χ²` comparison, and the
final rewrite from `‖p-q‖₁ = 2 D_{TV}(p,q)` to the quadratic TV certificate.

## Goal

`data.logChiSqBound ∧ data.tvQuadraticBound`

## Theorem docstring

Paper-facing wrapper for the explicit KL certificate obtained from a total-variation estimate
and a positive minimum atom of the reference law.
    lem:kl-from-tv-qmin

## DAG

Nodes (Prop fields):
- `sharedSupport` (leaf)
- `qMinPositive` (leaf)
- `chiSqControlledByL1` (derived)
- `klLeLogOnePlusChiSq` (leaf)
- `l1EqualsTwoTv` (leaf)
- `logChiSqBound` (derived)
- `tvQuadraticBound` (derived)

Edges:
- sharedSupport + qMinPositive  →  **chiSqControlledByL1**
- chiSqControlledByL1 + klLeLogOnePlusChiSq  →  **logChiSqBound**
- logChiSqBound + l1EqualsTwoTv  →  **tvQuadraticBound**

## Imports
- `Mathlib.Tactic`
