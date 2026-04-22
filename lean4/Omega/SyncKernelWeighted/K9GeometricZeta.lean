import Mathlib.Analysis.SpecificLimits.Normed

namespace Omega.SyncKernelWeighted

theorem paper_k9_geometric_zeta (z u : ℝ) (h : |(7 + 14 * u) * z| < 1) :
    (∑' n : ℕ, (((7 + 14 * u) * z) ^ n)) = 1 / (1 - (7 + 14 * u) * z) := by
  simpa [Real.norm_eq_abs, one_div] using
    (tsum_geometric_of_norm_lt_one (ξ := ((7 + 14 * u) * z)) (by
      simpa [Real.norm_eq_abs] using h))

end Omega.SyncKernelWeighted
