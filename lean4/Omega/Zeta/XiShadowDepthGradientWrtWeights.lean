import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-shadow-depth-gradient-wrt-weights`. -/
theorem paper_xi_shadow_depth_gradient_wrt_weights {κ : ℕ} (a w db : Fin κ → ℝ) (b : ℝ)
    (hdenom : 0 < ∑ j, w j / (a j - b) ^ 2)
    (hformula :
      ∀ k, db k = -(1 / (a k - b)) / ∑ j, w j / (a j - b) ^ 2) :
    (∀ k, a k < b → 0 < db k) ∧ (∀ k, b < a k → db k < 0) := by
  constructor
  · intro k hk
    have hdiff_neg : a k - b < 0 := sub_neg.mpr hk
    have hinv_neg : 1 / (a k - b) < 0 := by
      exact one_div_neg.mpr hdiff_neg
    have hnum_pos : 0 < -(1 / (a k - b)) := neg_pos.mpr hinv_neg
    rw [hformula k]
    exact div_pos hnum_pos hdenom
  · intro k hk
    have hdiff_pos : 0 < a k - b := sub_pos.mpr hk
    have hinv_pos : 0 < 1 / (a k - b) := by
      exact one_div_pos.mpr hdiff_pos
    have hnum_neg : -(1 / (a k - b)) < 0 := neg_neg_of_pos hinv_pos
    rw [hformula k]
    exact div_neg_of_neg_of_pos hnum_neg hdenom

end Omega.Zeta
