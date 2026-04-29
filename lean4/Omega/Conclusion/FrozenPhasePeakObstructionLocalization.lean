import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-frozen-phase-peak-obstruction-localization`. -/
theorem paper_conclusion_frozen_phase_peak_obstruction_localization
    (g_star alpha_star alpha2 a a_c beta_inv : ℝ) (h_theta : ℝ → ℝ)
    (hsep : alpha2 < alpha_star) (hfrozen : a_c < a)
    (hcollapse : ∀ theta : ℝ, 1 ≤ theta → h_theta theta = g_star)
    (hbeta : beta_inv = alpha_star / Real.log 2) :
    (∀ theta : ℝ, 1 ≤ theta → h_theta theta = g_star) ∧
      beta_inv = alpha_star / Real.log 2 ∧ alpha2 < alpha_star := by
  let _ := hfrozen
  exact ⟨hcollapse, hbeta, hsep⟩

end Omega.Conclusion
