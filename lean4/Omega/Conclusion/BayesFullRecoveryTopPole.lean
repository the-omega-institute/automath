import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Conclusion

noncomputable section

/-- Descending order predicate for the finite weight list. -/
def conclusion_bayes_full_recovery_top_pole_sorted_weights : List ℝ → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => a ≥ b ∧ conclusion_bayes_full_recovery_top_pole_sorted_weights (b :: rest)

/-- Dominant-pole data for the Bayes full-recovery coefficient sequence. -/
structure conclusion_bayes_full_recovery_top_pole_data where
  conclusion_bayes_full_recovery_top_pole_weights : List ℝ
  conclusion_bayes_full_recovery_top_pole_topMass : ℝ
  conclusion_bayes_full_recovery_top_pole_topMultiplicity : ℕ
  conclusion_bayes_full_recovery_top_pole_coeff : ℕ → ℝ
  conclusion_bayes_full_recovery_top_pole_dominantConstant : ℝ
  conclusion_bayes_full_recovery_top_pole_sortedWeights :
    conclusion_bayes_full_recovery_top_pole_sorted_weights
      conclusion_bayes_full_recovery_top_pole_weights
  conclusion_bayes_full_recovery_top_pole_ratio_limit :
    Tendsto
      (fun t : ℕ =>
        conclusion_bayes_full_recovery_top_pole_coeff (t + 1) /
          conclusion_bayes_full_recovery_top_pole_coeff t)
      atTop
      (nhds conclusion_bayes_full_recovery_top_pole_topMass)
  conclusion_bayes_full_recovery_top_pole_multiplicity_limit :
    Tendsto
      (fun t : ℕ =>
        (t : ℝ) *
          (conclusion_bayes_full_recovery_top_pole_coeff (t + 1) /
                (conclusion_bayes_full_recovery_top_pole_topMass *
                  conclusion_bayes_full_recovery_top_pole_coeff t) -
              1))
      atTop
      (nhds ((conclusion_bayes_full_recovery_top_pole_topMultiplicity : ℝ) - 1))

/-- Ratio readout for the top mass from consecutive full-recovery coefficients. -/
def conclusion_bayes_full_recovery_top_pole_ratio
    (D : conclusion_bayes_full_recovery_top_pole_data) (t : ℕ) : ℝ :=
  D.conclusion_bayes_full_recovery_top_pole_coeff (t + 1) /
    D.conclusion_bayes_full_recovery_top_pole_coeff t

/-- First correction readout for the top multiplicity. -/
def conclusion_bayes_full_recovery_top_pole_multiplicity_profile
    (D : conclusion_bayes_full_recovery_top_pole_data) (t : ℕ) : ℝ :=
  (t : ℝ) *
    (D.conclusion_bayes_full_recovery_top_pole_coeff (t + 1) /
          (D.conclusion_bayes_full_recovery_top_pole_topMass *
            D.conclusion_bayes_full_recovery_top_pole_coeff t) -
        1)

/-- Concrete dominant-pole recovery statement for the top mass and its multiplicity. -/
def conclusion_bayes_full_recovery_top_pole_statement
    (D : conclusion_bayes_full_recovery_top_pole_data) : Prop :=
  conclusion_bayes_full_recovery_top_pole_sorted_weights
      D.conclusion_bayes_full_recovery_top_pole_weights ∧
    Tendsto (conclusion_bayes_full_recovery_top_pole_ratio D) atTop
      (nhds D.conclusion_bayes_full_recovery_top_pole_topMass) ∧
    Tendsto (conclusion_bayes_full_recovery_top_pole_multiplicity_profile D) atTop
      (nhds ((D.conclusion_bayes_full_recovery_top_pole_topMultiplicity : ℝ) - 1))

/-- Paper label: `thm:conclusion-bayes-full-recovery-top-pole`. -/
theorem paper_conclusion_bayes_full_recovery_top_pole
    (D : conclusion_bayes_full_recovery_top_pole_data) :
    conclusion_bayes_full_recovery_top_pole_statement D := by
  refine ⟨D.conclusion_bayes_full_recovery_top_pole_sortedWeights, ?_, ?_⟩
  · simpa [conclusion_bayes_full_recovery_top_pole_ratio] using
      D.conclusion_bayes_full_recovery_top_pole_ratio_limit
  · simpa [conclusion_bayes_full_recovery_top_pole_multiplicity_profile] using
      D.conclusion_bayes_full_recovery_top_pole_multiplicity_limit

end

end Omega.Conclusion
