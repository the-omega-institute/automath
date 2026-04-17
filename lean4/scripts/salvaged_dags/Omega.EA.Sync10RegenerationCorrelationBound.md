# Omega.EA.Sync10RegenerationCorrelationBound

- File: `Omega/EA/Sync10RegenerationCorrelationBound.lean`
- Struct: `Sync10RegenerationCorrelationBoundData`
- Paper label: `?`
- Goal theorem: `paper_sync10_regeneration_correlation_bound`

## Structure docstring

Chapter-local package for the sync-10 regeneration/correlation corollary. The data store the
reset-word witness `00000`, the common-input coupling argument, and the two paper-facing
consequences: pathwise coalescence after the first reset block and the resulting total-variation
estimate.

## Goal

`D.pathwiseCoalescenceBound ∧ D.totalVariationBound`

## Theorem docstring

Paper-facing wrapper for the sync-10 regeneration/correlation bound: once the reset block
`00000` appears, the common-input coupling forces the two trajectories to agree five steps later,
and the total-variation estimate follows from the usual coupling characterization.
    cor:sync10-regeneration-correlation-bound

## DAG

Nodes (Prop fields):
- `resetWordWitness` (leaf)
- `commonInputCoupling` (leaf)
- `pathwiseCoalescenceBound` (derived)
- `totalVariationBound` (derived)

Edges:
- resetWordWitness + commonInputCoupling  →  **pathwiseCoalescenceBound**
- pathwiseCoalescenceBound  →  **totalVariationBound**

## Imports
- `Mathlib.Tactic`
