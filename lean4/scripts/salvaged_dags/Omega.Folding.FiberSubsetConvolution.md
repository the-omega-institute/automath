# Omega.Folding.FiberSubsetConvolution

- File: `Omega/Folding/FiberSubsetConvolution.lean`
- Struct: `FoldFiberSubsetConvolutionData`
- Paper label: `prop:fold-fiber-subset-convolution`
- Goal theorem: `paper_fold_fiber_subset_convolution`

## Structure docstring

Chapter-local package for the fold-fiber subset-convolution identity. The data record the
all-zero pattern counts, the fixed pattern counts obtained by coordinate flips on a chosen subset,
and the powerset summation step turning the translate formula into the convolution formula.

## Goal

`D.zeroPatternTranslateFormula ∧ D.subsetConvolutionFormula`

## Theorem docstring

Paper-facing wrapper for the finite-coordinate fold-fiber subset convolution: the coordinate
flip bijection identifies each fixed-pattern count with a translate of the all-zero pattern count,
and summing these translates over the chosen powerset yields the convolution identity.
    prop:fold-fiber-subset-convolution

## DAG

Nodes (Prop fields):
- `zeroPatternCounts` (leaf)
- `fixedPatternCounts` (leaf)
- `coordinateFlipBijection` (leaf)
- `powersetSummation` (leaf)
- `zeroPatternTranslateFormula` (derived)
- `subsetConvolutionFormula` (derived)

Edges:
- zeroPatternCounts + fixedPatternCounts + coordinateFlipBijection  →  **zeroPatternTranslateFormula**
- zeroPatternTranslateFormula + powersetSummation  →  **subsetConvolutionFormula**

## Imports
- `Mathlib.Tactic`
