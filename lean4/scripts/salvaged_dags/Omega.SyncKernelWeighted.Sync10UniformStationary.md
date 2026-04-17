# Omega.SyncKernelWeighted.Sync10UniformStationary

- File: `Omega/SyncKernelWeighted/Sync10UniformStationary.lean`
- Struct: `Sync10UniformStationaryData`
- Paper label: `prop:sync10-uniform-stationary`
- Goal theorem: `paper_sync10_uniform_stationary`

## Structure docstring

Chapter-local wrapper for the exact 10-state stationary law of the uniform-input sync kernel.
The data record the finite 10-state Markov kernel, the rational transition weights, and the
candidate stationary vector whose entries sum to one and solve `πP = π` entrywise.

## Goal

`D.stateSpaceExact ∧ D.stationaryMassesExact`

## Theorem docstring

Paper-facing wrapper for the exact 10-state stationary distribution under uniform input.
Once the 10-state rational kernel and the candidate stationary vector are fixed, the state-space
description is exact and the listed rational masses satisfy the stationary equations.
    prop:sync10-uniform-stationary

## DAG

Nodes (Prop fields):
- `tenStateKernel` (leaf)
- `rationalTransitionWeights` (leaf)
- `candidateStationaryVector` (leaf)
- `stateSpaceExact` (derived)
- `stationaryMassesExact` (derived)

Edges:
- tenStateKernel + rationalTransitionWeights + candidateStationaryVector  →  **stateSpaceExact**
- stateSpaceExact  →  **stationaryMassesExact**

## Imports
- `Mathlib.Tactic`
