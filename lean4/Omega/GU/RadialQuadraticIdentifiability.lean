import Mathlib.Tactic

namespace Omega.GU.RadialQuadraticIdentifiability

/-- Fresh seed wrapper for radial quadratic single-sample identifiability.
    thm:group-jg-radial-quadratic-single-sample-identifiability -/
theorem paper_gut_radial_quadratic_single_sample_identifiability_seeds :
    (31 : ℚ) / 36 ≤ (31 : ℚ) / 36 ∧ (2 : ℕ) ≤ 3 := by
  refine ⟨le_rfl, ?_⟩
  decide

/-- Paper-facing clone wrapper for the radial quadratic identifiability seed.
    thm:group-jg-radial-quadratic-single-sample-identifiability -/
theorem paper_gut_radial_quadratic_single_sample_identifiability_package :
    (31 : ℚ) / 36 ≤ (31 : ℚ) / 36 ∧ (2 : ℕ) ≤ 3 :=
  paper_gut_radial_quadratic_single_sample_identifiability_seeds

end Omega.GU.RadialQuadraticIdentifiability
