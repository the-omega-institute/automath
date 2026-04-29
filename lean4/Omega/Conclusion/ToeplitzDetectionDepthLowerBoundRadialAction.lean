import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-toeplitz-detection-depth-lower-bound-radial-action`. -/
theorem paper_conclusion_toeplitz_detection_depth_lower_bound_radial_action {κ : ℕ}
    {A hmin Ndet c0 : ℝ} (hκ : 0 < κ) (hA : 0 < A) (hhmin : 0 < hmin) (hc0 : 0 < c0)
    (hdepth : hmin ≤ A / (κ : ℝ)) (hdetect : c0 / hmin ≤ Ndet) :
    ∃ c : ℝ, 0 < c ∧ c * (κ : ℝ) / A ≤ Ndet := by
  refine ⟨c0, hc0, ?_⟩
  have hκ_real : 0 < (κ : ℝ) := by exact_mod_cast hκ
  have hdepth_mul : hmin * (κ : ℝ) ≤ A := by
    exact (le_div_iff₀ hκ_real).mp hdepth
  have hle : (κ : ℝ) / A ≤ 1 / hmin := by
    rw [div_le_iff₀ hA]
    have hle_div : (κ : ℝ) ≤ A / hmin := by
      rw [le_div_iff₀ hhmin]
      nlinarith
    calc
      (κ : ℝ) ≤ A / hmin := hle_div
      _ = 1 / hmin * A := by ring
  calc
    c0 * (κ : ℝ) / A = c0 * ((κ : ℝ) / A) := by ring
    _ ≤ c0 * (1 / hmin) := mul_le_mul_of_nonneg_left hle hc0.le
    _ = c0 / hmin := by ring
    _ ≤ Ndet := hdetect

end Omega.Conclusion
