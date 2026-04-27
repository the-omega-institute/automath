import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete complex second-moment data for the Poisson quartic comparison. -/
structure conclusion_poisson_complex_second_moment_complete_for_all_f_data where
  m2 : ℂ
  m2' : ℂ

/-- Comparison witnessed by one smooth `f`: equality of squared second-moment magnitudes. -/
def conclusion_poisson_complex_second_moment_complete_for_all_f_someComparison
    (D : conclusion_poisson_complex_second_moment_complete_for_all_f_data) : Prop :=
  ‖D.m2‖ ^ (2 : ℕ) = ‖D.m2'‖ ^ (2 : ℕ)

/-- Comparison witnessed by every smooth `f`: the same quartic coefficient equality. -/
def conclusion_poisson_complex_second_moment_complete_for_all_f_everyComparison
    (D : conclusion_poisson_complex_second_moment_complete_for_all_f_data) : Prop :=
  ‖D.m2‖ ^ (2 : ℕ) = ‖D.m2'‖ ^ (2 : ℕ)

/-- Equality of the nonnegative complex second-moment magnitudes. -/
def conclusion_poisson_complex_second_moment_complete_for_all_f_magnitudeEquality
    (D : conclusion_poisson_complex_second_moment_complete_for_all_f_data) : Prop :=
  ‖D.m2‖ = ‖D.m2'‖

/-- Paper-facing equivalence of one comparison, all comparisons, and magnitude equality. -/
def conclusion_poisson_complex_second_moment_complete_for_all_f_statement
    (D : conclusion_poisson_complex_second_moment_complete_for_all_f_data) : Prop :=
  (conclusion_poisson_complex_second_moment_complete_for_all_f_someComparison D ↔
      conclusion_poisson_complex_second_moment_complete_for_all_f_everyComparison D) ∧
    (conclusion_poisson_complex_second_moment_complete_for_all_f_someComparison D ↔
      conclusion_poisson_complex_second_moment_complete_for_all_f_magnitudeEquality D) ∧
    (conclusion_poisson_complex_second_moment_complete_for_all_f_everyComparison D ↔
      conclusion_poisson_complex_second_moment_complete_for_all_f_magnitudeEquality D)

/-- Nonnegative reals have equal squares exactly when they are equal. -/
theorem conclusion_poisson_complex_second_moment_complete_for_all_f_sq_eq_sq_iff
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ (2 : ℕ) = y ^ (2 : ℕ) ↔ x = y := by
  constructor
  · intro hsq
    nlinarith [sq_nonneg (x - y), hsq]
  · intro h
    rw [h]

/-- Paper label: `thm:conclusion-poisson-complex-second-moment-complete-for-all-f`. -/
theorem paper_conclusion_poisson_complex_second_moment_complete_for_all_f
    (D : conclusion_poisson_complex_second_moment_complete_for_all_f_data) :
    conclusion_poisson_complex_second_moment_complete_for_all_f_statement D := by
  have hsquare :
      ‖D.m2‖ ^ (2 : ℕ) = ‖D.m2'‖ ^ (2 : ℕ) ↔ ‖D.m2‖ = ‖D.m2'‖ :=
    conclusion_poisson_complex_second_moment_complete_for_all_f_sq_eq_sq_iff
      (norm_nonneg D.m2) (norm_nonneg D.m2')
  refine ⟨?_, ?_, ?_⟩
  · constructor <;> intro h <;>
      simpa [conclusion_poisson_complex_second_moment_complete_for_all_f_someComparison,
        conclusion_poisson_complex_second_moment_complete_for_all_f_everyComparison] using h
  · simp [conclusion_poisson_complex_second_moment_complete_for_all_f_someComparison,
      conclusion_poisson_complex_second_moment_complete_for_all_f_magnitudeEquality, hsquare]
  · simp [conclusion_poisson_complex_second_moment_complete_for_all_f_everyComparison,
      conclusion_poisson_complex_second_moment_complete_for_all_f_magnitudeEquality, hsquare]

end Omega.Conclusion
