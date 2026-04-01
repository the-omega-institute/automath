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
  nlinarith [Real.sq_sqrt (show 0 ≤ (5 : ℝ) by positivity), Real.golden_sq]

/-- Square of the critical threshold.
    thm:conclusion-binfold-tail-order-statistics-single-jump-collapse -/
theorem epsilonCritical_sq : epsilonCritical^2 = Real.goldenRatio^2 / 5 := by
  unfold epsilonCritical
  have hs : (Real.sqrt 5)^2 = (5 : ℝ) := by rw [sq_abs, abs_of_nonneg (by positivity), Real.sq_sqrt (by positivity)]
  field_simp [hs]
  ring

end Omega.Conclusion
