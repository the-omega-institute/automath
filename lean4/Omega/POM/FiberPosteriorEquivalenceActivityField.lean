import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Omega.POM.FiberFullPosteriorUniformizationProductSource

namespace Omega.POM

/-- The concrete activity attached to the posterior at coordinate `j`. -/
noncomputable def posteriorActivityField (p : ℕ → ℝ) (j : ℕ) : ℝ :=
  posteriorOddsRatio (p j)

/-- Fiberwise posterior equivalence expressed as equality of the induced activity field. -/
def sameActivityField (m : ℕ) (p : ℕ → ℝ) : Prop :=
  ∀ j, j + 2 < m →
    posteriorActivityField p j =
      posteriorActivityField p (j + 1) * posteriorActivityField p (j + 2)

/-- The additive log-ratio form of the activity-field recurrence. -/
def logRatioRecurrence (m : ℕ) (p : ℕ → ℝ) : Prop :=
  ∀ j, j + 2 < m →
    Real.log (posteriorActivityField p j) =
      Real.log (posteriorActivityField p (j + 1)) +
        Real.log (posteriorActivityField p (j + 2))

lemma sameActivityField_iff_logRatioRecurrence
    {m : ℕ} {p : ℕ → ℝ}
    (hp0 : ∀ j, 0 < p j) (hp1 : ∀ j, p j < 1) :
    sameActivityField m p ↔ logRatioRecurrence m p := by
  constructor
  · intro h j hj
    have hj0 : 0 < posteriorActivityField p j := posteriorOddsRatio_pos (hp0 j) (hp1 j)
    have hj1 : 0 < posteriorActivityField p (j + 1) :=
      posteriorOddsRatio_pos (hp0 (j + 1)) (hp1 (j + 1))
    have hj2 : 0 < posteriorActivityField p (j + 2) :=
      posteriorOddsRatio_pos (hp0 (j + 2)) (hp1 (j + 2))
    rw [show posteriorActivityField p j =
        posteriorActivityField p (j + 1) * posteriorActivityField p (j + 2) from h j hj]
    rw [Real.log_mul (ne_of_gt hj1) (ne_of_gt hj2)]
  · intro h j hj
    have hj0 : 0 < posteriorActivityField p j := posteriorOddsRatio_pos (hp0 j) (hp1 j)
    have hj1 : 0 < posteriorActivityField p (j + 1) :=
      posteriorOddsRatio_pos (hp0 (j + 1)) (hp1 (j + 1))
    have hj2 : 0 < posteriorActivityField p (j + 2) :=
      posteriorOddsRatio_pos (hp0 (j + 2)) (hp1 (j + 2))
    have hexp := congrArg Real.exp (h j hj)
    simpa [Real.exp_add, Real.exp_log hj0, Real.exp_log hj1, Real.exp_log hj2] using hexp

/-- Full posterior uniformization on a fiber is equivalent to equality of the induced activity
field, and for positive posterior coordinates this multiplicative recurrence is equivalent to the
additive log-ratio recurrence.
    thm:pom-fiber-posterior-equivalence-activity-field -/
theorem paper_pom_fiber_posterior_equivalence_activity_field
    (m : ℕ) (hm : 3 ≤ m) (p : ℕ → ℝ)
    (hp0 : ∀ j, 0 < p j) (hp1 : ∀ j, p j < 1) :
    (fullPosteriorUniformizationProductSource m p ↔ sameActivityField m p) ∧
      (sameActivityField m p ↔ logRatioRecurrence m p) := by
  refine ⟨?_, sameActivityField_iff_logRatioRecurrence hp0 hp1⟩
  simpa [sameActivityField, posteriorActivityField, posteriorUniformTrigger] using
    (paper_pom_fiber_full_posterior_uniformization_product_source m hm p).1

end Omega.POM
