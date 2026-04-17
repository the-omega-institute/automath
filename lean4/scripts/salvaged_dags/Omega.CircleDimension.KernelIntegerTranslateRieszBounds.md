# Omega.CircleDimension.KernelIntegerTranslateRieszBounds

- File: `Omega/CircleDimension/KernelIntegerTranslateRieszBounds.lean`
- Struct: `KernelIntegerTranslateRieszBoundsData`
- Paper label: `prop:cdim-kernel-integer-translate-riesz-bounds`
- Goal theorem: `paper_cdim_kernel_integer_translate_riesz_bounds`

## Structure docstring

Chapter-local wrapper for the integer-translate Riesz package attached to the difference
kernel `K(a,b) = 2 / (4 + (a - b)^2)`. The fields record that the Toeplitz symbol has been
assembled from the RKHS feature-map and lattice-sampling interfaces, that its sharp minimum and
maximum have been identified, and that these extrema have been converted into the Riesz basis and
the optimal frame bounds.

## Goal

`D.rieszBasis ∧ D.sharpLowerBound ∧ D.sharpUpperBound`

## Theorem docstring

Paper-facing wrapper for the sharp Riesz bounds of the integer translates of the
CircleDimension kernel `K(a,b) = 2 / (4 + (a - b)^2)`.
    prop:cdim-kernel-integer-translate-riesz-bounds

## DAG

Nodes (Prop fields):
- `toeplitzSymbolComputed` (leaf)
- `sharpMinValueIdentified` (derived)
- `sharpMaxValueIdentified` (derived)
- `rieszBasis` (derived)
- `sharpLowerBound` (derived)
- `sharpUpperBound` (derived)

Edges:
- toeplitzSymbolComputed  →  **sharpMinValueIdentified**
- toeplitzSymbolComputed  →  **sharpMaxValueIdentified**
- sharpMinValueIdentified + sharpMaxValueIdentified  →  **rieszBasis**
- sharpMinValueIdentified  →  **sharpLowerBound**
- sharpMaxValueIdentified  →  **sharpUpperBound**

## Imports
- `Mathlib.Tactic`
- `Omega.CircleDimension.KernelRKHSFeatureMap`
- `Omega.CircleDimension.PoissonLatticeSampling`
