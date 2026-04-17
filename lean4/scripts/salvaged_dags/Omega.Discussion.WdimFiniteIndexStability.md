# Omega.Discussion.WdimFiniteIndexStability

- File: `Omega/Discussion/WdimFiniteIndexStability.lean`
- Struct: `WdimFiniteIndexStabilityData`
- Paper label: `?`
- Goal theorem: `paper_discussion_wdim_finite_index_stability`

## Structure docstring

Chapter-local wrapper for the finite-index stability of the weighted Stokes character
dimension. The structure stores the finite-index invariance statement for signed circle
dimension, the identification `wdim = cdim^±`, and the final transport of stability across that
identity.

## Goal

`D.wdimStable`

## Theorem docstring

Paper-facing wrapper for the discussion corollary: finite-index stability of signed circle
dimension, combined with the identity `wdim = cdim^±`, yields finite-index stability of `wdim`.
    cor:discussion-wdim-finite-index-stability

## DAG

Nodes (Prop fields):
- `signedCircleFiniteIndexStable` (leaf)
- `wdimEqSignedCircleDimension` (leaf)
- `wdimStable` (derived)

Edges:
- signedCircleFiniteIndexStable + wdimEqSignedCircleDimension  →  **wdimStable**

## Imports
- `Mathlib.Tactic`
- `Omega.CircleDimension.SignedCircleDimension`
