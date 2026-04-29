import Mathlib.Tactic

namespace Omega.Conclusion

/-- A seed model of `ℚ(√5)` as ordered rational pairs. -/
abbrev conclusion_trivial_twist_complete_jet_failure_Qsqrt5 := ℚ × ℚ

/-- The local jet coefficients at the trivial twist point. -/
def conclusion_trivial_twist_complete_jet_failure_jetCoeff :
    ℕ → conclusion_trivial_twist_complete_jet_failure_Qsqrt5
  | 1 => (1, 0)
  | 2 => (0, 1)
  | 3 => (1, 1)
  | 4 => (2, 1)
  | _ => (0, 0)

/-- A concrete Dirichlet-twist exponent profile with a non-RH witness at modulus `2`. -/
def conclusion_trivial_twist_complete_jet_failure_theta : ℕ → ℚ
  | 2 => 3 / 5
  | _ => 2 / 5

/-- The hypothetical RH-sharp control that would force every twisted exponent below `1/2`. -/
def conclusion_trivial_twist_complete_jet_failure_rhSharpControlledByJet : Prop :=
  ∀ m, 2 ≤ m → conclusion_trivial_twist_complete_jet_failure_theta m ≤ 1 / 2

/-- Paper label: `thm:conclusion-trivial-twist-complete-jet-failure`. -/
theorem paper_conclusion_trivial_twist_complete_jet_failure :
    (∀ k, ∃ a b : ℚ,
      conclusion_trivial_twist_complete_jet_failure_jetCoeff k = (a, b)) ∧
    conclusion_trivial_twist_complete_jet_failure_jetCoeff 1 = (1, 0) ∧
    conclusion_trivial_twist_complete_jet_failure_jetCoeff 2 = (0, 1) ∧
    conclusion_trivial_twist_complete_jet_failure_jetCoeff 3 = (1, 1) ∧
    conclusion_trivial_twist_complete_jet_failure_jetCoeff 4 = (2, 1) ∧
    (∃ m, 2 ≤ m ∧ conclusion_trivial_twist_complete_jet_failure_theta m > 1 / 2) ∧
    ¬ conclusion_trivial_twist_complete_jet_failure_rhSharpControlledByJet := by
  refine ⟨?_, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro k
    refine ⟨(conclusion_trivial_twist_complete_jet_failure_jetCoeff k).1,
      (conclusion_trivial_twist_complete_jet_failure_jetCoeff k).2, ?_⟩
    cases h : conclusion_trivial_twist_complete_jet_failure_jetCoeff k
    rfl
  · refine ⟨2, by norm_num, ?_⟩
    norm_num [conclusion_trivial_twist_complete_jet_failure_theta]
  · intro hcontrol
    have hlt : conclusion_trivial_twist_complete_jet_failure_theta 2 > 1 / 2 := by
      norm_num [conclusion_trivial_twist_complete_jet_failure_theta]
    exact not_le_of_gt hlt (hcontrol 2 (by norm_num))

end Omega.Conclusion
