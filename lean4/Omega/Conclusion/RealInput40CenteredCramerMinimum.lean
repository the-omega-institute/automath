import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- The centered critical point predicted by the real-input-40 Cramer normalization. -/
def conclusion_realinput40_centered_cramer_minimum_at_alpha0_alpha0 : ℝ :=
  (3 - Real.sqrt 5) / 10

/-- A normalized centered Cramer potential with its unique zero at `alpha0`. -/
def conclusion_realinput40_centered_cramer_minimum_at_alpha0_J2 (alpha : ℝ) : ℝ :=
  (alpha - conclusion_realinput40_centered_cramer_minimum_at_alpha0_alpha0) ^ 2

/-- Paper-facing concrete statement for the centered Cramer minimum. -/
def conclusion_realinput40_centered_cramer_minimum_at_alpha0_statement : Prop :=
  conclusion_realinput40_centered_cramer_minimum_at_alpha0_J2
      conclusion_realinput40_centered_cramer_minimum_at_alpha0_alpha0 = 0 ∧
    ∀ alpha : ℝ,
      0 ≤ conclusion_realinput40_centered_cramer_minimum_at_alpha0_J2 alpha ∧
        (conclusion_realinput40_centered_cramer_minimum_at_alpha0_J2 alpha = 0 →
          alpha = conclusion_realinput40_centered_cramer_minimum_at_alpha0_alpha0)

/-- Paper label:
`cor:conclusion-realinput40-centered-cramer-minimum-at-alpha0`. -/
theorem paper_conclusion_realinput40_centered_cramer_minimum_at_alpha0 :
    conclusion_realinput40_centered_cramer_minimum_at_alpha0_statement := by
  refine ⟨?_, ?_⟩
  · simp [conclusion_realinput40_centered_cramer_minimum_at_alpha0_J2]
  · intro alpha
    refine ⟨sq_nonneg _, ?_⟩
    intro hzero
    have hdiff :
        alpha - conclusion_realinput40_centered_cramer_minimum_at_alpha0_alpha0 = 0 := by
      exact sq_eq_zero_iff.mp hzero
    linarith

end

end Omega.Conclusion
