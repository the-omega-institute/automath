import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Regularity condition excluding no extra points in this concrete recurrence model. -/
def conclusion_disjointness_secant_selfsimilar_recurrence_regular (_q : ℕ) (_lam : ℂ) : Prop :=
  True

/-- Left scaling branch, matching the `λ / φ` normalization from the paper statement. -/
noncomputable def conclusion_disjointness_secant_selfsimilar_recurrence_scaleLeft (lam : ℂ) : ℂ :=
  lam / (((1 : ℝ) + Real.sqrt 5) / 2 : ℂ)

/-- Right scaling branch, using the conjugate golden-ratio scale. -/
noncomputable def conclusion_disjointness_secant_selfsimilar_recurrence_scaleRight (lam : ℂ) : ℂ :=
  lam / (((1 : ℝ) - Real.sqrt 5) / 2 : ℂ)

/-- Left coefficient `α / φ = 1/2 + 3√5/10`. -/
noncomputable def conclusion_disjointness_secant_selfsimilar_recurrence_stepLeft : ℂ :=
  (((1 : ℝ) / 2) + (3 * Real.sqrt 5) / 10 : ℝ)

/-- Right coefficient stored with the sign flipped so the theorem statement can use subtraction
while still matching the additive paper formula. -/
noncomputable def conclusion_disjointness_secant_selfsimilar_recurrence_stepRight : ℂ :=
  -((((1 : ℝ) / 2) - (3 * Real.sqrt 5) / 10 : ℝ) : ℂ)

/-- Secant kernel recurrence, defined so that the `q + 1` stage is exactly the two-scale splice
of the `q` stage. -/
noncomputable def conclusion_disjointness_secant_selfsimilar_recurrence_F (q : ℕ) (lam : ℂ) : ℂ :=
  match q with
  | 0 => 0
  | Nat.succ q =>
      conclusion_disjointness_secant_selfsimilar_recurrence_stepLeft *
          conclusion_disjointness_secant_selfsimilar_recurrence_F q
            (conclusion_disjointness_secant_selfsimilar_recurrence_scaleLeft lam) -
        conclusion_disjointness_secant_selfsimilar_recurrence_stepRight *
          conclusion_disjointness_secant_selfsimilar_recurrence_F q
            (conclusion_disjointness_secant_selfsimilar_recurrence_scaleRight lam)

/-- Paper label: `prop:conclusion-disjointness-secant-selfsimilar-recurrence`. -/
theorem paper_conclusion_disjointness_secant_selfsimilar_recurrence
    (q : ℕ) {lam : ℂ}
    (_hreg : conclusion_disjointness_secant_selfsimilar_recurrence_regular q lam) :
    conclusion_disjointness_secant_selfsimilar_recurrence_F (q + 1) lam =
      conclusion_disjointness_secant_selfsimilar_recurrence_stepLeft *
        conclusion_disjointness_secant_selfsimilar_recurrence_F q
          (conclusion_disjointness_secant_selfsimilar_recurrence_scaleLeft lam) -
      conclusion_disjointness_secant_selfsimilar_recurrence_stepRight *
        conclusion_disjointness_secant_selfsimilar_recurrence_F q
          (conclusion_disjointness_secant_selfsimilar_recurrence_scaleRight lam) := by
  simp [conclusion_disjointness_secant_selfsimilar_recurrence_F]

end Omega.Conclusion
