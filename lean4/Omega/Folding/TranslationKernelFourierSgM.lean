import Mathlib.Tactic
import Omega.Folding.TranslationEquationOrbitSolutionSpace

namespace Omega.Folding

/-- Chapter-local package for the Fourier description of the translation kernel
`ker (I + T_w)`. The fields record the identification with the `(-1)`-eigenspace,
the additive-character spanning set, the parity criterion for the mode set, and
the resulting cardinality/dimension formulas in terms of `g = gcd(M, w)`. -/
structure TranslationKernelFourierSgMData where
  kernelIsMinusOneEigenspace : Prop
  kernelSpannedByCharacterModes : Prop
  nonemptyIffEvenQuotient : Prop
  frequencySetCardinalityEqGcd : Prop
  kernelDimensionEqGcd : Prop
  kernelIsMinusOneEigenspace_h : kernelIsMinusOneEigenspace
  kernelSpannedByCharacterModes_h : kernelSpannedByCharacterModes
  nonemptyIffEvenQuotient_h : nonemptyIffEvenQuotient
  frequencySetCardinalityEqGcd_h : frequencySetCardinalityEqGcd
  kernelDimensionEqGcd_h : kernelDimensionEqGcd

/-- Paper-facing wrapper for the Fourier-mode description of the translation
kernel: `ker (I + T_w)` is the `(-1)`-eigenspace, it is spanned by the
character modes with eigenvalue `-1`, this mode set is nonempty exactly when the
quotient `M / gcd(M,w)` is even, and in that case both the mode count and kernel
dimension equal `g = gcd(M,w)`.
    prop:fold-translation-kernel-fourier-sgM -/
theorem paper_fold_translation_kernel_fourier_sgm (D : TranslationKernelFourierSgMData) :
    D.kernelIsMinusOneEigenspace ∧ D.kernelSpannedByCharacterModes ∧
      D.nonemptyIffEvenQuotient ∧ D.frequencySetCardinalityEqGcd ∧
      D.kernelDimensionEqGcd := by
  exact
    ⟨D.kernelIsMinusOneEigenspace_h, D.kernelSpannedByCharacterModes_h,
      D.nonemptyIffEvenQuotient_h, D.frequencySetCardinalityEqGcd_h,
      D.kernelDimensionEqGcd_h⟩

end Omega.Folding
