import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete Boolean data for the structural NULL/reject/oracle trichotomy.  Removing the
NULL/oracle branch forces a total pass/reject finite certificate closure; the bundled collapse
obstruction says that such a total finite closure triggers the encoded `P = NP` flag. -/
structure conclusion_null_reject_oracle_trichotomy_structural_data where
  conclusion_null_reject_oracle_trichotomy_structural_nullOracleBranch : Bool
  conclusion_null_reject_oracle_trichotomy_structural_totalPassRejectFiniteClosure : Bool
  conclusion_null_reject_oracle_trichotomy_structural_pEqualsNP : Bool
  conclusion_null_reject_oracle_trichotomy_structural_closure_of_no_null_oracle :
    conclusion_null_reject_oracle_trichotomy_structural_nullOracleBranch = false →
      conclusion_null_reject_oracle_trichotomy_structural_totalPassRejectFiniteClosure = true
  conclusion_null_reject_oracle_trichotomy_structural_collapse_obstruction :
    conclusion_null_reject_oracle_trichotomy_structural_totalPassRejectFiniteClosure = true →
      conclusion_null_reject_oracle_trichotomy_structural_pEqualsNP = true

/-- The structural trichotomy: either the third branch remains present, or total finite closure is
not available, or the encoded complexity collapse has occurred. -/
def conclusion_null_reject_oracle_trichotomy_structural_statement
    (D : conclusion_null_reject_oracle_trichotomy_structural_data) : Prop :=
  D.conclusion_null_reject_oracle_trichotomy_structural_nullOracleBranch = true ∨
    D.conclusion_null_reject_oracle_trichotomy_structural_totalPassRejectFiniteClosure = false ∨
    D.conclusion_null_reject_oracle_trichotomy_structural_pEqualsNP = true

/-- Paper label: `cor:conclusion-null-reject-oracle-trichotomy-structural`. -/
theorem paper_conclusion_null_reject_oracle_trichotomy_structural
    (D : conclusion_null_reject_oracle_trichotomy_structural_data) :
    conclusion_null_reject_oracle_trichotomy_structural_statement D := by
  by_cases hnull :
      D.conclusion_null_reject_oracle_trichotomy_structural_nullOracleBranch = true
  · exact Or.inl hnull
  · right
    right
    have hnullFalse :
        D.conclusion_null_reject_oracle_trichotomy_structural_nullOracleBranch = false := by
      cases h :
          D.conclusion_null_reject_oracle_trichotomy_structural_nullOracleBranch
      · rfl
      · exact False.elim (hnull h)
    have hforced :
        D.conclusion_null_reject_oracle_trichotomy_structural_totalPassRejectFiniteClosure = true :=
      D.conclusion_null_reject_oracle_trichotomy_structural_closure_of_no_null_oracle hnullFalse
    exact D.conclusion_null_reject_oracle_trichotomy_structural_collapse_obstruction hforced

end Omega.Conclusion
