import Mathlib.Data.Real.Basic

namespace Omega.Zeta

/-- Paper label: `prop:xi-poisson-variance-mismatch-tv-leading`. -/
theorem paper_xi_poisson_variance_mismatch_tv_leading
    (tvLeading varianceGap constant : ℝ) (hconstant : 0 < constant)
    (hleading : tvLeading = constant * |varianceGap|) :
    0 ≤ tvLeading ∧ (varianceGap = 0 → tvLeading = 0) := by
  constructor
  · rw [hleading]
    exact mul_nonneg (le_of_lt hconstant) (abs_nonneg varianceGap)
  · intro hgap
    rw [hleading, hgap, abs_zero, mul_zero]

end Omega.Zeta
