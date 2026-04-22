import Mathlib.Tactic
import Omega.Conclusion.GoldenSprtDeltaClosure

namespace Omega.POM

/-- The exact symmetric-threshold SPRT error formula, restated in the POM chapter from the
closed-form golden-SPRT error curve.
    thm:pom-sprt-symmetric-threshold-error -/
theorem paper_pom_sprt_symmetric_threshold_error (T : ℕ) :
    Omega.Conclusion.goldenSprtErrorPhi (T : ℝ) = 1 / (1 + Real.goldenRatio ^ (T : ℝ)) ∧
      1 - Omega.Conclusion.goldenSprtErrorPhi (T : ℝ) =
        Real.goldenRatio ^ (T : ℝ) / (1 + Real.goldenRatio ^ (T : ℝ)) := by
  constructor
  · rfl
  · unfold Omega.Conclusion.goldenSprtErrorPhi
    have hdenom : 1 + Real.goldenRatio ^ (T : ℝ) ≠ 0 := by positivity
    field_simp [hdenom]
    ring

end Omega.POM
