import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-frozen-phase-statistical-inversion-exponent-splitting`. The
freezing law fixes every entropy exponent to `g_star`, the inversion law identifies
`beta_inv = alpha_star / log 2`, and substituting both gives the uniform constant-gap formula. -/
theorem paper_conclusion_frozen_phase_statistical_inversion_exponent_splitting
    (g_star alpha_star : ℝ) (h_theta : ℝ → ℝ) (beta_inv : ℝ)
    (h_freeze : ∀ theta : ℝ, h_theta theta = g_star)
    (h_inv : beta_inv = alpha_star / Real.log 2) :
    (∀ theta : ℝ, h_theta theta = g_star) ∧
      beta_inv = alpha_star / Real.log 2 ∧
      ∀ theta : ℝ, (Real.log 2) * beta_inv - h_theta theta = alpha_star - g_star := by
  refine ⟨h_freeze, h_inv, ?_⟩
  intro theta
  rw [h_freeze theta, h_inv]
  have hlog : Real.log 2 ≠ 0 := by
    exact Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  rw [mul_div_cancel₀ alpha_star hlog]

end Omega.Conclusion
