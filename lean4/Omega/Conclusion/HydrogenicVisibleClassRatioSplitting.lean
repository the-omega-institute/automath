import Mathlib.Tactic
import Omega.Folding.Window6

namespace Omega.Conclusion

/-- Total hydrogenic shell-cardinality. -/
def conclusion_hydrogenic_visible_class_ratio_splitting_address_card (n : ℕ) : ℕ :=
  2 * n ^ 2

/-- Visible class count for the class-function collapse. -/
def conclusion_hydrogenic_visible_class_ratio_splitting_classfunction_card (n : ℕ) : ℕ :=
  n

/-- Visible class count for the phase-blind collapse. -/
def conclusion_hydrogenic_visible_class_ratio_splitting_phaseblind_card (n : ℕ) : ℕ :=
  n * (n + 1) / 2

/-- Real ratio for the class-function quotient. -/
noncomputable def conclusion_hydrogenic_visible_class_ratio_splitting_classfunction_ratio
    (n : ℕ) : ℝ :=
  1 / (2 * n)

/-- Real ratio for the phase-blind quotient. -/
noncomputable def conclusion_hydrogenic_visible_class_ratio_splitting_phaseblind_ratio
    (n : ℕ) : ℝ :=
  (n + 1 : ℝ) / (4 * n)

/-- The concrete ratio-splitting statement packages the three exact cardinalities and the two ratio
rewrites; for `n = 0` the ratio part is suppressed to avoid division by zero. -/
def conclusion_hydrogenic_visible_class_ratio_splitting_stmt (n : ℕ) : Prop :=
  conclusion_hydrogenic_visible_class_ratio_splitting_address_card n = 2 * n ^ 2 ∧
    conclusion_hydrogenic_visible_class_ratio_splitting_classfunction_card n = n ∧
    conclusion_hydrogenic_visible_class_ratio_splitting_phaseblind_card n = n * (n + 1) / 2 ∧
    (n = 0 ∨
      (conclusion_hydrogenic_visible_class_ratio_splitting_classfunction_ratio n =
          1 / (2 * n) ∧
        conclusion_hydrogenic_visible_class_ratio_splitting_phaseblind_ratio n =
          (n + 1) / (4 * n)))

/-- Paper label: `cor:conclusion-hydrogenic-visible-class-ratio-splitting`. -/
theorem paper_conclusion_hydrogenic_visible_class_ratio_splitting
    (n : Nat) : conclusion_hydrogenic_visible_class_ratio_splitting_stmt n := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  by_cases hn : n = 0
  · exact Or.inl hn
  · right
    simp [conclusion_hydrogenic_visible_class_ratio_splitting_classfunction_ratio,
      conclusion_hydrogenic_visible_class_ratio_splitting_phaseblind_ratio]

end Omega.Conclusion
