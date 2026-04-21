import Omega.GU.JoukowskyGodelPullbackFactorization

namespace Omega.GU

open Omega.GU.LeyangHolographicN2

variable {K : Type*} [Field K]

/-- Exact paper-facing holographic identity in the degree-`2` setting. -/
theorem paper_group_jg_leyang_holographic_identity
    (r z z₁ z₂ : K) (hr : r ≠ 0) (hz : z ≠ 0) :
    Q_r_eval_at_J r z z₁ z₂ = r ^ 2 * P z z₁ z₂ * P ((r ^ 2)⁻¹ * z⁻¹) z₁ z₂ := by
  have hden : r ^ 2 * z ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero 2 hr) (pow_ne_zero 2 hz)
  clear hden
  simpa using Q_r_eval_at_J_eq r z z₁ z₂

end Omega.GU
