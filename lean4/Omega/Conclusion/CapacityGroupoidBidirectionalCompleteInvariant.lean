import Mathlib.Tactic
import Omega.DerivedConsequences.DerivedWindow6GroupoidElliottBoundaryFace

namespace Omega.Conclusion

open Omega.DerivedConsequences

/-- Concrete multiplicity histogram used by the conclusion-level bidirectional reconstruction. -/
def conclusion_capacity_groupoid_bidirectional_complete_invariant_histogram (d : ℕ) : ℕ :=
  if d = 2 then 8 else if d = 3 then 4 else if d = 4 then 9 else 0

/-- Continuous capacity curve specialized to the rigid histogram `(8, 4, 9)` on degrees
`(2, 3, 4)`. -/
def conclusion_capacity_groupoid_bidirectional_complete_invariant_capacity_curve (T : ℕ) : ℕ :=
  8 * min 2 T + 4 * min 3 T + 9 * min 4 T

/-- Discrete first difference of the capacity curve. -/
def conclusion_capacity_groupoid_bidirectional_complete_invariant_tail_count (t : ℕ) : ℕ :=
  conclusion_capacity_groupoid_bidirectional_complete_invariant_capacity_curve t -
    conclusion_capacity_groupoid_bidirectional_complete_invariant_capacity_curve (t - 1)

/-- Discrete second difference recovering the exact multiplicity histogram. -/
def conclusion_capacity_groupoid_bidirectional_complete_invariant_recovered_histogram (d : ℕ) : ℕ :=
  conclusion_capacity_groupoid_bidirectional_complete_invariant_tail_count d -
    conclusion_capacity_groupoid_bidirectional_complete_invariant_tail_count (d + 1)

/-- Wedderburn package imported from the window-`6` groupoid algebra decomposition. -/
def conclusion_capacity_groupoid_bidirectional_complete_invariant_wedderburn_package : Prop :=
  let D : derived_window6_groupoid_elliott_boundary_face_data := { witness := () }
  D.wedderburn_decomposition

/-- The capacity curve, its discrete differences, and the window-`6` groupoid algebra carry the
same rigid histogram data. -/
def conclusion_capacity_groupoid_bidirectional_complete_invariant_statement : Prop :=
  conclusion_capacity_groupoid_bidirectional_complete_invariant_histogram 2 = 8 ∧
    conclusion_capacity_groupoid_bidirectional_complete_invariant_histogram 3 = 4 ∧
    conclusion_capacity_groupoid_bidirectional_complete_invariant_histogram 4 = 9 ∧
    conclusion_capacity_groupoid_bidirectional_complete_invariant_tail_count 1 = 21 ∧
    conclusion_capacity_groupoid_bidirectional_complete_invariant_tail_count 2 = 21 ∧
    conclusion_capacity_groupoid_bidirectional_complete_invariant_tail_count 3 = 13 ∧
    conclusion_capacity_groupoid_bidirectional_complete_invariant_tail_count 4 = 9 ∧
    conclusion_capacity_groupoid_bidirectional_complete_invariant_tail_count 5 = 0 ∧
    conclusion_capacity_groupoid_bidirectional_complete_invariant_recovered_histogram 2 = 8 ∧
    conclusion_capacity_groupoid_bidirectional_complete_invariant_recovered_histogram 3 = 4 ∧
    conclusion_capacity_groupoid_bidirectional_complete_invariant_recovered_histogram 4 = 9 ∧
    conclusion_capacity_groupoid_bidirectional_complete_invariant_recovered_histogram 5 = 0 ∧
    (∀ T : ℕ,
      conclusion_capacity_groupoid_bidirectional_complete_invariant_capacity_curve T =
        conclusion_capacity_groupoid_bidirectional_complete_invariant_histogram 2 * min 2 T +
          conclusion_capacity_groupoid_bidirectional_complete_invariant_histogram 3 * min 3 T +
            conclusion_capacity_groupoid_bidirectional_complete_invariant_histogram 4 * min 4 T) ∧
    conclusion_capacity_groupoid_bidirectional_complete_invariant_wedderburn_package

/-- Paper label: `thm:conclusion-capacity-groupoid-bidirectional-complete-invariant`. -/
theorem paper_conclusion_capacity_groupoid_bidirectional_complete_invariant :
    conclusion_capacity_groupoid_bidirectional_complete_invariant_statement := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, ?_, ?_⟩
  · intro T
    simp [conclusion_capacity_groupoid_bidirectional_complete_invariant_capacity_curve,
      conclusion_capacity_groupoid_bidirectional_complete_invariant_histogram]
  · simpa [conclusion_capacity_groupoid_bidirectional_complete_invariant_wedderburn_package] using
      (paper_derived_window6_groupoid_elliott_boundary_face
        ({ witness := () } : derived_window6_groupoid_elliott_boundary_face_data)).1

end Omega.Conclusion
