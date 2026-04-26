import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete completed-defect package for the mixed-semiring product law. -/
structure conclusion_completed_defect_mixed_semiring_data where
  leftMultiplicity : ℕ
  rightMultiplicity : ℕ
  leftBlaschkeAction : ℝ
  rightBlaschkeAction : ℝ
  leftInteriorRadius : ℝ
  rightInteriorRadius : ℝ

/-- Zero multiplicities add under product. -/
def conclusion_completed_defect_mixed_semiring_productMultiplicity
    (D : conclusion_completed_defect_mixed_semiring_data) : ℕ :=
  D.leftMultiplicity + D.rightMultiplicity

/-- Blaschke actions add under product. -/
def conclusion_completed_defect_mixed_semiring_productAction
    (D : conclusion_completed_defect_mixed_semiring_data) : ℝ :=
  D.leftBlaschkeAction + D.rightBlaschkeAction

/-- The maximal interior radius of the product package. -/
def conclusion_completed_defect_mixed_semiring_productInteriorRadius
    (D : conclusion_completed_defect_mixed_semiring_data) : ℝ :=
  max D.leftInteriorRadius D.rightInteriorRadius

/-- Boundary depth is measured by complementing the interior radius. -/
def conclusion_completed_defect_mixed_semiring_boundaryDepth (r : ℝ) : ℝ :=
  1 - r

/-- The max-radius rule is equivalent to a min rule for boundary depth. -/
lemma conclusion_completed_defect_mixed_semiring_boundaryDepth_max
    (r s : ℝ) :
    conclusion_completed_defect_mixed_semiring_boundaryDepth (max r s) =
      min (conclusion_completed_defect_mixed_semiring_boundaryDepth r)
        (conclusion_completed_defect_mixed_semiring_boundaryDepth s) := by
  by_cases h : r ≤ s
  · have hdepth : 1 - s ≤ 1 - r := by linarith
    simp [conclusion_completed_defect_mixed_semiring_boundaryDepth, max_eq_right h,
      min_eq_right hdepth]
  · have h' : s ≤ r := le_of_not_ge h
    have hdepth : 1 - r ≤ 1 - s := by linarith
    simp [conclusion_completed_defect_mixed_semiring_boundaryDepth, max_eq_left h',
      min_eq_left hdepth]

/-- Paper-facing statement for the completed-defect mixed semiring package. -/
def conclusion_completed_defect_mixed_semiring_statement
    (D : conclusion_completed_defect_mixed_semiring_data) : Prop :=
  conclusion_completed_defect_mixed_semiring_productMultiplicity D =
      D.leftMultiplicity + D.rightMultiplicity ∧
    conclusion_completed_defect_mixed_semiring_productAction D =
      D.leftBlaschkeAction + D.rightBlaschkeAction ∧
    conclusion_completed_defect_mixed_semiring_productInteriorRadius D =
      max D.leftInteriorRadius D.rightInteriorRadius ∧
    conclusion_completed_defect_mixed_semiring_boundaryDepth
        (conclusion_completed_defect_mixed_semiring_productInteriorRadius D) =
      min
        (conclusion_completed_defect_mixed_semiring_boundaryDepth D.leftInteriorRadius)
        (conclusion_completed_defect_mixed_semiring_boundaryDepth D.rightInteriorRadius)

/-- Paper label: `thm:conclusion-completed-defect-mixed-semiring`. In the completed-defect model,
zero multiplicities and Blaschke actions add under product, the interior radius is the larger of
the two factors, and the associated boundary depth is therefore their minimum. -/
theorem paper_conclusion_completed_defect_mixed_semiring
    (D : conclusion_completed_defect_mixed_semiring_data) :
    conclusion_completed_defect_mixed_semiring_statement D := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  simpa [conclusion_completed_defect_mixed_semiring_productInteriorRadius] using
    conclusion_completed_defect_mixed_semiring_boundaryDepth_max
      D.leftInteriorRadius D.rightInteriorRadius

end Omega.Conclusion
