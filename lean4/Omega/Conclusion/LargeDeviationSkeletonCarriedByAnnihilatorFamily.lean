import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete package for the integer pressure anchors carried by the annihilator-polynomial family.
The annihilator and initial block determine the whole integer sequence, whose Perron growth then
feeds the pressure anchor. -/
structure conclusion_large_deviation_skeleton_carried_by_annihilator_family_data where
  conclusion_large_deviation_skeleton_carried_by_annihilator_family_annihilator :
    ∀ q : ℕ, 2 ≤ q → List ℤ
  conclusion_large_deviation_skeleton_carried_by_annihilator_family_initial_block :
    ∀ q : ℕ, 2 ≤ q → List ℤ
  conclusion_large_deviation_skeleton_carried_by_annihilator_family_sequence :
    ∀ q : ℕ, 2 ≤ q → ℕ → ℤ
  conclusion_large_deviation_skeleton_carried_by_annihilator_family_sequence_from_data :
    List ℤ → List ℤ → ℕ → ℤ
  conclusion_large_deviation_skeleton_carried_by_annihilator_family_perron_growth :
    ∀ q : ℕ, 2 ≤ q → ℝ
  conclusion_large_deviation_skeleton_carried_by_annihilator_family_perron_readout :
    (ℕ → ℤ) → ℝ
  conclusion_large_deviation_skeleton_carried_by_annihilator_family_integer_pressure :
    ℕ → ℝ
  conclusion_large_deviation_skeleton_carried_by_annihilator_family_sequence_determined :
    ∀ (q : ℕ) (hq : 2 ≤ q) n,
      conclusion_large_deviation_skeleton_carried_by_annihilator_family_sequence_from_data
          (conclusion_large_deviation_skeleton_carried_by_annihilator_family_annihilator q hq)
          (conclusion_large_deviation_skeleton_carried_by_annihilator_family_initial_block q hq) n =
        conclusion_large_deviation_skeleton_carried_by_annihilator_family_sequence q hq n
  conclusion_large_deviation_skeleton_carried_by_annihilator_family_growth_readout :
    ∀ (q : ℕ) (hq : 2 ≤ q),
      conclusion_large_deviation_skeleton_carried_by_annihilator_family_perron_growth q hq =
        conclusion_large_deviation_skeleton_carried_by_annihilator_family_perron_readout
          (conclusion_large_deviation_skeleton_carried_by_annihilator_family_sequence q hq)
  conclusion_large_deviation_skeleton_carried_by_annihilator_family_pressure_anchor :
    ∀ (q : ℕ) (hq : 2 ≤ q),
      conclusion_large_deviation_skeleton_carried_by_annihilator_family_integer_pressure (q - 1) =
        Real.log
            (conclusion_large_deviation_skeleton_carried_by_annihilator_family_perron_growth q hq) -
          Real.log 2

/-- The integer pressure values are determined by the annihilator family plus its minimal initial
blocks. -/
def conclusion_large_deviation_skeleton_carried_by_annihilator_family_statement
    (D : conclusion_large_deviation_skeleton_carried_by_annihilator_family_data) : Prop :=
  ∀ (q : ℕ) (hq : 2 ≤ q),
    D.conclusion_large_deviation_skeleton_carried_by_annihilator_family_integer_pressure (q - 1) =
      Real.log
          (D.conclusion_large_deviation_skeleton_carried_by_annihilator_family_perron_readout
            (D.conclusion_large_deviation_skeleton_carried_by_annihilator_family_sequence_from_data
              (D.conclusion_large_deviation_skeleton_carried_by_annihilator_family_annihilator q hq)
              (D.conclusion_large_deviation_skeleton_carried_by_annihilator_family_initial_block q hq))) -
        Real.log 2

/-- Paper label: `thm:conclusion-large-deviation-skeleton-carried-by-annihilator-family`. -/
theorem paper_conclusion_large_deviation_skeleton_carried_by_annihilator_family
    (D : conclusion_large_deviation_skeleton_carried_by_annihilator_family_data) :
    conclusion_large_deviation_skeleton_carried_by_annihilator_family_statement D := by
  intro q hq
  rw [D.conclusion_large_deviation_skeleton_carried_by_annihilator_family_pressure_anchor q hq]
  rw [D.conclusion_large_deviation_skeleton_carried_by_annihilator_family_growth_readout q hq]
  have hseq :
      D.conclusion_large_deviation_skeleton_carried_by_annihilator_family_sequence q hq =
        D.conclusion_large_deviation_skeleton_carried_by_annihilator_family_sequence_from_data
          (D.conclusion_large_deviation_skeleton_carried_by_annihilator_family_annihilator q hq)
          (D.conclusion_large_deviation_skeleton_carried_by_annihilator_family_initial_block q hq) := by
    funext n
    exact
      (D.conclusion_large_deviation_skeleton_carried_by_annihilator_family_sequence_determined
        q hq n).symm
  rw [hseq]

end Omega.Conclusion
