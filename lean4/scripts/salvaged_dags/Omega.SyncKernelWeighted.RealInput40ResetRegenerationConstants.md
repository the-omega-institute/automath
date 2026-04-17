# Omega.SyncKernelWeighted.RealInput40ResetRegenerationConstants

- File: `Omega/SyncKernelWeighted/RealInput40ResetRegenerationConstants.lean`
- Struct: `RealInput40ResetRegenerationConstantsData`
- Paper label: `prop:real-input-40-reset-regeneration-constants`
- Goal theorem: `paper_real_input_40_reset_regeneration_constants`

## Structure docstring

Chapter-local wrapper for the closed-form reset-sector regeneration constants. The fields store
the three paper-facing outputs: the reset-sector mass, the Kac return-time identity, and the
conditioned waiting-time constant from the finite-state hitting chain.

## Goal

`D.resetSectorMassClosed ∧ D.kacReturnTimeClosed ∧ D.conditionalWaitClosed`

## Theorem docstring

Paper-facing wrapper for the reset-sector regeneration constants.
    prop:real-input-40-reset-regeneration-constants

## DAG

Nodes (Prop fields):
- `resetSectorMassClosed` (leaf)
- `kacReturnTimeClosed` (leaf)
- `conditionalWaitClosed` (leaf)

Edges:
- (none)

## Imports
- `Mathlib.Tactic`
