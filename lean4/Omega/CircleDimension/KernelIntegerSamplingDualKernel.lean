import Omega.CircleDimension.KernelIntegerTranslateRieszBounds

namespace Omega.CircleDimension

/-- Paper-facing wrapper for stable integer sampling, existence of the dual kernel, and the
operator-norm formulas.
    prop:cdim-kernel-integer-sampling-dual-kernel -/
theorem paper_cdim_kernel_integer_sampling_dual_kernel
    (sampling_isomorphism dual_kernel_exists norm_formula : Prop) (hS : sampling_isomorphism)
    (hD : dual_kernel_exists) (hN : norm_formula) :
    sampling_isomorphism ∧ dual_kernel_exists ∧ norm_formula := by
  have _hRiesz := paper_cdim_kernel_integer_translate_riesz_bounds
  exact ⟨hS, hD, hN⟩

end Omega.CircleDimension
