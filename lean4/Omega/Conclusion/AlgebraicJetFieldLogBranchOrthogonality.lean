import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Concrete algebraic-jet/log-branch data.  The algebraic closure is represented by an actual set
of real numbers; recursive implicit differentiation keeps every jet coordinate in that set, while
the selected logarithmic branch coordinate is certified outside it. -/
structure conclusion_algebraic_jet_field_log_branch_orthogonality_data where
  conclusion_algebraic_jet_field_log_branch_orthogonality_algebraicField : Set ℝ
  conclusion_algebraic_jet_field_log_branch_orthogonality_jet : ℕ → ℝ
  conclusion_algebraic_jet_field_log_branch_orthogonality_logBranch : ℕ → ℝ
  conclusion_algebraic_jet_field_log_branch_orthogonality_logIndex : ℕ
  conclusion_algebraic_jet_field_log_branch_orthogonality_initial_jet_mem :
    conclusion_algebraic_jet_field_log_branch_orthogonality_jet 0 ∈
      conclusion_algebraic_jet_field_log_branch_orthogonality_algebraicField
  conclusion_algebraic_jet_field_log_branch_orthogonality_implicit_step_mem :
    ∀ n,
      conclusion_algebraic_jet_field_log_branch_orthogonality_jet n ∈
          conclusion_algebraic_jet_field_log_branch_orthogonality_algebraicField →
        conclusion_algebraic_jet_field_log_branch_orthogonality_jet (n + 1) ∈
          conclusion_algebraic_jet_field_log_branch_orthogonality_algebraicField
  conclusion_algebraic_jet_field_log_branch_orthogonality_log_branch_transcendent :
    conclusion_algebraic_jet_field_log_branch_orthogonality_logBranch
        conclusion_algebraic_jet_field_log_branch_orthogonality_logIndex ∉
      conclusion_algebraic_jet_field_log_branch_orthogonality_algebraicField

namespace conclusion_algebraic_jet_field_log_branch_orthogonality_data

/-- Every recursively generated jet coordinate remains in the algebraic field. -/
def conclusion_algebraic_jet_field_log_branch_orthogonality_allJetsAlgebraic
    (D : conclusion_algebraic_jet_field_log_branch_orthogonality_data) : Prop :=
  ∀ n,
    D.conclusion_algebraic_jet_field_log_branch_orthogonality_jet n ∈
      D.conclusion_algebraic_jet_field_log_branch_orthogonality_algebraicField

/-- The distinguished logarithmic branch coordinate is outside the algebraic field. -/
def conclusion_algebraic_jet_field_log_branch_orthogonality_logBranchOutside
    (D : conclusion_algebraic_jet_field_log_branch_orthogonality_data) : Prop :=
  D.conclusion_algebraic_jet_field_log_branch_orthogonality_logBranch
      D.conclusion_algebraic_jet_field_log_branch_orthogonality_logIndex ∉
    D.conclusion_algebraic_jet_field_log_branch_orthogonality_algebraicField

/-- Orthogonality means no algebraic jet coordinate can equal the selected logarithmic branch
coordinate. -/
def conclusion_algebraic_jet_field_log_branch_orthogonality_noJetHitsLogBranch
    (D : conclusion_algebraic_jet_field_log_branch_orthogonality_data) : Prop :=
  ∀ n,
    D.conclusion_algebraic_jet_field_log_branch_orthogonality_jet n ≠
      D.conclusion_algebraic_jet_field_log_branch_orthogonality_logBranch
        D.conclusion_algebraic_jet_field_log_branch_orthogonality_logIndex

/-- Paper-facing algebraic/logarithmic orthogonality package. -/
def conclusion_algebraic_jet_field_log_branch_orthogonality_statement
    (D : conclusion_algebraic_jet_field_log_branch_orthogonality_data) : Prop :=
  D.conclusion_algebraic_jet_field_log_branch_orthogonality_allJetsAlgebraic ∧
    D.conclusion_algebraic_jet_field_log_branch_orthogonality_logBranchOutside ∧
      D.conclusion_algebraic_jet_field_log_branch_orthogonality_noJetHitsLogBranch

end conclusion_algebraic_jet_field_log_branch_orthogonality_data

open conclusion_algebraic_jet_field_log_branch_orthogonality_data

lemma conclusion_algebraic_jet_field_log_branch_orthogonality_all_jets_mem
    (D : conclusion_algebraic_jet_field_log_branch_orthogonality_data) :
    D.conclusion_algebraic_jet_field_log_branch_orthogonality_allJetsAlgebraic := by
  intro n
  induction n with
  | zero =>
      exact D.conclusion_algebraic_jet_field_log_branch_orthogonality_initial_jet_mem
  | succ n ih =>
      exact
        D.conclusion_algebraic_jet_field_log_branch_orthogonality_implicit_step_mem n ih

/-- Paper label: `thm:conclusion-algebraic-jet-field-log-branch-orthogonality`. -/
theorem paper_conclusion_algebraic_jet_field_log_branch_orthogonality
    (D : conclusion_algebraic_jet_field_log_branch_orthogonality_data) :
    conclusion_algebraic_jet_field_log_branch_orthogonality_statement D := by
  have hJets :
      D.conclusion_algebraic_jet_field_log_branch_orthogonality_allJetsAlgebraic :=
    conclusion_algebraic_jet_field_log_branch_orthogonality_all_jets_mem D
  have hLog :
      D.conclusion_algebraic_jet_field_log_branch_orthogonality_logBranchOutside :=
    D.conclusion_algebraic_jet_field_log_branch_orthogonality_log_branch_transcendent
  refine ⟨hJets, hLog, ?_⟩
  intro n hEq
  exact hLog (hEq ▸ hJets n)

end

end Omega.Conclusion
