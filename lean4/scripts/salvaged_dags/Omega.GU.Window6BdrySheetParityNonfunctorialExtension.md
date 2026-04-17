# Omega.GU.Window6BdrySheetParityNonfunctorialExtension

- File: `Omega/GU/Window6BdrySheetParityNonfunctorialExtension.lean`
- Struct: `Window6BdrySheetParityData`
- Paper label: `thm:window6-bdry-sheet-parity-nonfunctorial-extension`
- Goal theorem: `paper_window6_bdry_sheet_parity_nonfunctorial_extension`

## Structure docstring

Chapter-local package for the nonfunctorial boundary-sheet parity extension at window `6`.
The paper proof combines the even-fiber existence criterion for free involutions with the
fiberwise double-factorial count and the audited boundary multiplicities at `m = 6, 7, 8`.

## Goal

`h.existsIffAllBoundaryFibersEven ∧ h.countEqFiberwiseDoubleFactorial ∧ h.auditValuesM6M7M8`

## Theorem docstring

Paper-facing wrapper for the window-`6` boundary-sheet parity extension: the chapter-local
data records the existence criterion, the fiberwise double-factorial count, and the audited
boundary values at `m = 6, 7, 8`.
    thm:window6-bdry-sheet-parity-nonfunctorial-extension

## DAG

Nodes (Prop fields):
- `existsIffAllBoundaryFibersEven` (leaf)
- `countEqFiberwiseDoubleFactorial` (leaf)
- `auditValuesM6M7M8` (leaf)

Edges:
- (none)

## Imports
- `Mathlib.Tactic`
- `Omega.GU.FreeInvolutionCount`
