import Mathlib.Tactic
import Omega.Conclusion.Window6Collision
import Omega.Conclusion.Window6RepresentationZetaCountRatio

namespace Omega.Conclusion

/-- The audited three-atom multiplicity measure for window `6`. -/
def conclusion_window6_threeatomic_measure_capacity_representation_measure (t : ℕ) : ℕ :=
  Omega.cBinFiberHist 6 t

/-- Capacity curve obtained by summing `min (2^B, t)` against the audited three-atom measure. -/
def conclusion_window6_threeatomic_measure_capacity_representation_capacity (B : ℕ) : ℕ :=
  Finset.sum ({2, 3, 4} : Finset ℕ) fun t =>
    conclusion_window6_threeatomic_measure_capacity_representation_measure t * min t (2 ^ B)

/-- Representation-side atom attached to the audited window-`6` zeta-count certificate. -/
def conclusion_window6_threeatomic_measure_capacity_representation_rep_atom (t : ℕ) : ℕ :=
  if t = 2 then 2 else if t = 3 then 3 else if t = 4 then 5 else 1

/-- Representation-count certificate obtained from the same three-atom data. -/
def conclusion_window6_threeatomic_measure_capacity_representation_representation_count : ℕ :=
  Finset.prod ({2, 3, 4} : Finset ℕ) fun t =>
    conclusion_window6_threeatomic_measure_capacity_representation_rep_atom t ^
      conclusion_window6_threeatomic_measure_capacity_representation_measure t

/-- Paper label: `thm:conclusion-window6-threeatomic-measure-capacity-representation`. -/
theorem paper_conclusion_window6_threeatomic_measure_capacity_representation :
    conclusion_window6_threeatomic_measure_capacity_representation_measure 2 = 8 ∧
      conclusion_window6_threeatomic_measure_capacity_representation_measure 3 = 4 ∧
      conclusion_window6_threeatomic_measure_capacity_representation_measure 4 = 9 ∧
      conclusion_window6_threeatomic_measure_capacity_representation_capacity 0 = 21 ∧
      conclusion_window6_threeatomic_measure_capacity_representation_capacity 1 = 42 ∧
      (∀ B : ℕ, 2 ≤ B →
        conclusion_window6_threeatomic_measure_capacity_representation_capacity B = 64) ∧
      conclusion_window6_threeatomic_measure_capacity_representation_representation_count =
        2 ^ 8 * 3 ^ 4 * 5 ^ 9 ∧
      conclusion_window6_threeatomic_measure_capacity_representation_representation_count =
        40500000000 := by
  rcases paper_conclusion_window6_representation_zeta_count_ratio with
    ⟨hrep, _, _, _, hhist⟩
  rcases hhist with ⟨h2, h3, h4⟩
  rcases Omega.conclusion_window6_capacity_bifurcation with ⟨hB0, hB1, hBge2⟩
  refine ⟨h2, h3, h4, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [conclusion_window6_threeatomic_measure_capacity_representation_capacity,
      conclusion_window6_threeatomic_measure_capacity_representation_measure, h2, h3, h4, add_assoc]
      using hB0
  · simpa [conclusion_window6_threeatomic_measure_capacity_representation_capacity,
      conclusion_window6_threeatomic_measure_capacity_representation_measure, h2, h3, h4, add_assoc]
      using hB1
  · intro B hB
    simpa [conclusion_window6_threeatomic_measure_capacity_representation_capacity,
      conclusion_window6_threeatomic_measure_capacity_representation_measure, h2, h3, h4, add_assoc]
      using hBge2 B hB
  · simpa [conclusion_window6_threeatomic_measure_capacity_representation_representation_count,
      conclusion_window6_threeatomic_measure_capacity_representation_rep_atom,
      conclusion_window6_threeatomic_measure_capacity_representation_measure, h2, h3, h4]
  · calc
      conclusion_window6_threeatomic_measure_capacity_representation_representation_count =
          2 ^ 8 * 3 ^ 4 * 5 ^ 9 := by
            simp [conclusion_window6_threeatomic_measure_capacity_representation_representation_count,
              conclusion_window6_threeatomic_measure_capacity_representation_rep_atom,
              conclusion_window6_threeatomic_measure_capacity_representation_measure, h2, h3, h4]
      _ = 40500000000 := hrep

end Omega.Conclusion
