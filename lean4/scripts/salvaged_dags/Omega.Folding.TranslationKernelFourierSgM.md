# Omega.Folding.TranslationKernelFourierSgM

- File: `Omega/Folding/TranslationKernelFourierSgM.lean`
- Struct: `TranslationKernelFourierSgMData`
- Paper label: `prop:fold-translation-kernel-fourier-sgM`
- Goal theorem: `paper_fold_translation_kernel_fourier_sgm`

## Structure docstring

Chapter-local package for the Fourier description of the translation kernel
`ker (I + T_w)`. The fields record the identification with the `(-1)`-eigenspace,
the additive-character spanning set, the parity criterion for the mode set, and
the resulting cardinality/dimension formulas in terms of `g = gcd(M, w)`.

## Goal

`D.kernelIsMinusOneEigenspace ∧ D.kernelSpannedByCharacterModes ∧ D.nonemptyIffEvenQuotient ∧ D.frequencySetCardinalityEqGcd ∧ D.kernelDimensionEqGcd`

## Theorem docstring

Paper-facing wrapper for the Fourier-mode description of the translation
kernel: `ker (I + T_w)` is the `(-1)`-eigenspace, it is spanned by the
character modes with eigenvalue `-1`, this mode set is nonempty exactly when the
quotient `M / gcd(M,w)` is even, and in that case both the mode count and kernel
dimension equal `g = gcd(M,w)`.
    prop:fold-translation-kernel-fourier-sgM

## DAG

Nodes (Prop fields):
- `kernelIsMinusOneEigenspace` (leaf)
- `kernelSpannedByCharacterModes` (leaf)
- `nonemptyIffEvenQuotient` (leaf)
- `frequencySetCardinalityEqGcd` (leaf)
- `kernelDimensionEqGcd` (leaf)

Edges:
- (none)

## Imports
- `Mathlib.Tactic`
- `Omega.Folding.TranslationEquationOrbitSolutionSpace`
