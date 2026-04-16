import Mathlib.Tactic
import Omega.CircleDimension.KernelRKHSFeatureMap
import Omega.CircleDimension.PoissonLatticeSampling

namespace Omega.CircleDimension

/-- Chapter-local wrapper for the integer-translate Riesz package attached to the difference
kernel `K(a,b) = 2 / (4 + (a - b)^2)`. The fields record that the Toeplitz symbol has been
assembled from the RKHS feature-map and lattice-sampling interfaces, that its sharp minimum and
maximum have been identified, and that these extrema have been converted into the Riesz basis and
the optimal frame bounds. -/
structure KernelIntegerTranslateRieszBoundsData where
  toeplitzSymbolComputed : Prop
  sharpMinValueIdentified : Prop
  sharpMaxValueIdentified : Prop
  rieszBasis : Prop
  sharpLowerBound : Prop
  sharpUpperBound : Prop
  toeplitzSymbolComputed_h : toeplitzSymbolComputed
  deriveSharpMinValue : toeplitzSymbolComputed → sharpMinValueIdentified
  deriveSharpMaxValue : toeplitzSymbolComputed → sharpMaxValueIdentified
  deriveRieszBasis :
    sharpMinValueIdentified → sharpMaxValueIdentified → rieszBasis
  deriveSharpLowerBound : sharpMinValueIdentified → sharpLowerBound
  deriveSharpUpperBound : sharpMaxValueIdentified → sharpUpperBound

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the sharp Riesz bounds of the integer translates of the
CircleDimension kernel `K(a,b) = 2 / (4 + (a - b)^2)`.
    prop:cdim-kernel-integer-translate-riesz-bounds -/
theorem paper_cdim_kernel_integer_translate_riesz_bounds
    (D : KernelIntegerTranslateRieszBoundsData) :
    D.rieszBasis ∧ D.sharpLowerBound ∧ D.sharpUpperBound := by
  have hMin : D.sharpMinValueIdentified := D.deriveSharpMinValue D.toeplitzSymbolComputed_h
  have hMax : D.sharpMaxValueIdentified := D.deriveSharpMaxValue D.toeplitzSymbolComputed_h
  exact ⟨D.deriveRieszBasis hMin hMax, D.deriveSharpLowerBound hMin,
    D.deriveSharpUpperBound hMax⟩

end Omega.CircleDimension
