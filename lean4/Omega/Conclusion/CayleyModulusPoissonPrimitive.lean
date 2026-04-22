import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-cayley-modulus-poisson-primitive`. -/
theorem paper_conclusion_cayley_modulus_poisson_primitive (u delta : ℝ) :
    -Real.log (Real.sqrt ((u^2 + (1 - delta)^2) / (u^2 + (1 + delta)^2))) =
      (1 / 2 : ℝ) * Real.log ((u^2 + (1 + delta)^2) / (u^2 + (1 - delta)^2)) := by
  let a : ℝ := u^2 + (1 - delta)^2
  let b : ℝ := u^2 + (1 + delta)^2
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hb_nonneg : 0 ≤ b := by
    dsimp [b]
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hab_inv : (a / b : ℝ)⁻¹ = b / a := by
    by_cases ha : a = 0
    · simp [ha]
    · by_cases hb : b = 0
      · simp [hb]
      · field_simp [ha, hb]
  calc
    -Real.log (Real.sqrt (a / b)) = -(Real.log (a / b) / 2) := by
      rw [Real.log_sqrt (div_nonneg ha_nonneg hb_nonneg)]
    _ = (1 / 2 : ℝ) * Real.log ((a / b : ℝ)⁻¹) := by
      rw [Real.log_inv]
      ring
    _ = (1 / 2 : ℝ) * Real.log (b / a) := by rw [hab_inv]
    _ = (1 / 2 : ℝ) * Real.log ((u^2 + (1 + delta)^2) / (u^2 + (1 - delta)^2)) := by
      simp [a, b]

end Omega.Conclusion
