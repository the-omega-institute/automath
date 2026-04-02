import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable def epsilonCritical : ℝ := Real.goldenRatio / Real.sqrt 5

/-- Positivity of the critical two-atom threshold.
    thm:conclusion-binfold-tail-order-statistics-single-jump-collapse -/
theorem epsilonCritical_pos : 0 < epsilonCritical := by
  unfold epsilonCritical
  positivity

/-- The critical threshold lies below 1.
    thm:conclusion-binfold-tail-order-statistics-single-jump-collapse -/
theorem epsilonCritical_lt_one : epsilonCritical < 1 := by
  unfold epsilonCritical
  have hsqrt5_pos : 0 < Real.sqrt 5 := by positivity
  have hsqrt5_gt_one : 1 < Real.sqrt 5 := by
    have hsq : (Real.sqrt 5)^2 = (5 : ℝ) := by
      rw [Real.sq_sqrt (show 0 ≤ (5 : ℝ) by positivity)]
    nlinarith
  have hφ_lt : Real.goldenRatio < Real.sqrt 5 := by
    rw [Real.goldenRatio]
    nlinarith
  exact (div_lt_one hsqrt5_pos).2 hφ_lt

/-- The critical threshold lies in the open unit interval.
    thm:conclusion-binfold-tail-order-statistics-single-jump-collapse -/
theorem epsilonCritical_mem_Ioo : epsilonCritical ∈ Set.Ioo (0 : ℝ) 1 := by
  exact ⟨epsilonCritical_pos, epsilonCritical_lt_one⟩

/-- Square of the critical threshold.
    thm:conclusion-binfold-tail-order-statistics-single-jump-collapse -/
theorem epsilonCritical_sq : epsilonCritical^2 = Real.goldenRatio^2 / 5 := by
  unfold epsilonCritical
  rw [div_pow, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by positivity)]

end Omega.Conclusion
