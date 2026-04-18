import Mathlib.Tactic

namespace Omega.Discussion

/-- Concrete model for a critical-line zero event. -/
def criticalLineZeroEvent (θ : ℤ) : Prop :=
  θ = 0

/-- Concrete model for the unitary-slice crossing event. -/
def unitarySliceCrossing (θ : ℤ) : Prop :=
  θ = 0

/-- Concrete winding index in the discussion model. -/
def windingIndex (κ : ℤ) : ℤ :=
  κ

/-- Concrete Blaschke degree in the discussion model. -/
def blaschkeDegree (κ : ℤ) : ℤ :=
  κ

/-- The integer defect index attached to a point defect. -/
def pointDefectIndex (κ : ℤ) : ℤ :=
  blaschkeDegree κ

/-- A point defect is visible exactly when its integer index is nonzero. -/
def pointDefectVisible (κ : ℤ) : Prop :=
  pointDefectIndex κ ≠ 0

theorem crossing_iff_critical_line_zero (θ : ℤ) :
    unitarySliceCrossing θ ↔ criticalLineZeroEvent θ := by
  rfl

/-- Paper-facing single-point crossing reformulation of the critical-line event.
    thm:discussion-critical-line-single-point-crossing -/
theorem paper_discussion_critical_line_single_point_crossing (θ : ℤ) :
    unitarySliceCrossing θ ↔ criticalLineZeroEvent θ := by
  simpa using crossing_iff_critical_line_zero θ

theorem winding_eq_blaschke (κ : ℤ) :
    windingIndex κ = blaschkeDegree κ := by
  rfl

theorem point_defect_classified_by_integer_index (κ : ℤ) :
    pointDefectVisible κ ↔ pointDefectIndex κ ≠ 0 := by
  rfl

theorem zero_degree_necessary_for_no_point_defect (κ : ℤ) :
    ¬ pointDefectVisible κ → blaschkeDegree κ = 0 := by
  simp [pointDefectVisible, pointDefectIndex, blaschkeDegree]

/-- Paper-facing concrete package for the crossing / winding / Blaschke index discussion.
    thm:discussion-crossing-winding-blaschke-index -/
theorem paper_discussion_crossing_winding_blaschke_index :
    (∀ θ : ℤ, unitarySliceCrossing θ ↔ criticalLineZeroEvent θ) ∧
      (∀ κ : ℤ, windingIndex κ = blaschkeDegree κ) ∧
      (∀ κ : ℤ, pointDefectVisible κ ↔ pointDefectIndex κ ≠ 0) ∧
      (∀ κ : ℤ, ¬ pointDefectVisible κ → blaschkeDegree κ = 0) := by
  exact ⟨crossing_iff_critical_line_zero, winding_eq_blaschke,
    point_defect_classified_by_integer_index, zero_degree_necessary_for_no_point_defect⟩

end Omega.Discussion
