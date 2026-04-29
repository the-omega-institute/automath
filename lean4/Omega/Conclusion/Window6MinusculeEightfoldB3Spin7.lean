import Mathlib.Tactic

namespace Omega.Conclusion

/-- The finite Lie-type dichotomy used by the window-`6` selection. -/
inductive conclusion_window6_minuscule_eightfold_b3_spin7_type
  | B3
  | C3
  deriving DecidableEq

/-- The minuscule orbit cardinality in the `B3/C3` dichotomy. -/
def conclusion_window6_minuscule_eightfold_b3_spin7_minusculeOrbitCard :
    conclusion_window6_minuscule_eightfold_b3_spin7_type → ℕ
  | .B3 => 8
  | .C3 => 6

/-- Concrete finite selection statement: an eightfold minuscule orbit selects `B3`, not `C3`. -/
def conclusion_window6_minuscule_eightfold_b3_spin7_statement : Prop :=
  conclusion_window6_minuscule_eightfold_b3_spin7_minusculeOrbitCard
      conclusion_window6_minuscule_eightfold_b3_spin7_type.B3 =
      8 ∧
    conclusion_window6_minuscule_eightfold_b3_spin7_minusculeOrbitCard
        conclusion_window6_minuscule_eightfold_b3_spin7_type.C3 =
        6 ∧
    (∀ T : conclusion_window6_minuscule_eightfold_b3_spin7_type,
      conclusion_window6_minuscule_eightfold_b3_spin7_minusculeOrbitCard T = 8 →
        T = conclusion_window6_minuscule_eightfold_b3_spin7_type.B3) ∧
    conclusion_window6_minuscule_eightfold_b3_spin7_minusculeOrbitCard
        conclusion_window6_minuscule_eightfold_b3_spin7_type.C3 ≠
      8

/-- Paper label: `thm:conclusion-window6-minuscule-eightfold-b3-spin7`. -/
theorem paper_conclusion_window6_minuscule_eightfold_b3_spin7 :
    conclusion_window6_minuscule_eightfold_b3_spin7_statement := by
  refine ⟨rfl, rfl, ?_, by norm_num [conclusion_window6_minuscule_eightfold_b3_spin7_minusculeOrbitCard]⟩
  intro T hT
  cases T <;> simp [conclusion_window6_minuscule_eightfold_b3_spin7_minusculeOrbitCard] at hT ⊢

end Omega.Conclusion
