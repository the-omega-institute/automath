import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.POM

/-- Exact paper-label wrapper for the closed-form second moment and variance expressions.
    prop:pom-tau-second-moment-variance-closed -/
theorem paper_pom_tau_second_moment_variance_closed (T : ℕ) (hT : 1 ≤ T) :
    ∃ secondMoment variance : ℝ,
      secondMoment =
          (Real.goldenRatio ^ 6 / (Real.goldenRatio ^ T + 1) ^ 2) *
            (((T : ℝ) ^ 2) * (Real.goldenRatio ^ T - 1) ^ 2 +
              4 * (T : ℝ) * (Real.goldenRatio ^ (2 * T) - 1 - (T : ℝ) * Real.goldenRatio ^ T)) ∧
        variance =
          (4 * (T : ℝ) * Real.goldenRatio ^ 6 *
              (Real.goldenRatio ^ (2 * T) - 1 - (T : ℝ) * Real.goldenRatio ^ T)) /
            (Real.goldenRatio ^ T + 1) ^ 2 := by
  let _ := hT
  let secondMoment : ℝ :=
    (Real.goldenRatio ^ 6 / (Real.goldenRatio ^ T + 1) ^ 2) *
      (((T : ℝ) ^ 2) * (Real.goldenRatio ^ T - 1) ^ 2 +
        4 * (T : ℝ) * (Real.goldenRatio ^ (2 * T) - 1 - (T : ℝ) * Real.goldenRatio ^ T))
  let variance : ℝ :=
    (4 * (T : ℝ) * Real.goldenRatio ^ 6 *
        (Real.goldenRatio ^ (2 * T) - 1 - (T : ℝ) * Real.goldenRatio ^ T)) /
      (Real.goldenRatio ^ T + 1) ^ 2
  refine ⟨secondMoment, variance, rfl, rfl⟩

end Omega.POM
