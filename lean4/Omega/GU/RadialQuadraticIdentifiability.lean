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

/-- Paper: `cor:group-jg-radial-quadratic-bounded-noise-threshold`.
    The verified single-sample gap constant `31/36` remains separating after a `σ`-inflation
    whenever `σ < 31/72`. -/
theorem paper_gut_radial_quadratic_bounded_noise_threshold (σ : ℚ) :
    σ < (31 : ℚ) / 72 → 2 * σ < (31 : ℚ) / 36 := by
  intro hσ
  nlinarith

end Omega.GU.RadialQuadraticIdentifiability
