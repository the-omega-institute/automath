import Mathlib.Data.Nat.Find
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Exact identification by a decision tree with `queryBudget` queries and `answerCount` answers. -/
def conclusion_oracle_fixedhistogram_nearexhaustive_query_lowerbound_identifies
    (candidateCount answerCount queryBudget : ℕ) : Prop :=
  candidateCount ≤ answerCount ^ queryBudget

/-- The least query count whose answer leaves can cover all fixed-histogram candidates. -/
noncomputable def conclusion_oracle_fixedhistogram_nearexhaustive_query_lowerbound_lowerBound
    (candidateCount answerCount : ℕ) : ℕ :=
  by
    classical
    exact if h : ∃ q, candidateCount ≤ answerCount ^ q then Nat.find h else 0

/-- Paper label: `thm:conclusion-oracle-fixedhistogram-nearexhaustive-query-lowerbound`. -/
theorem paper_conclusion_oracle_fixedhistogram_nearexhaustive_query_lowerbound
    (candidateCount answerCount queryBudget : Nat)
    (hIdentifies :
      conclusion_oracle_fixedhistogram_nearexhaustive_query_lowerbound_identifies candidateCount
        answerCount queryBudget) :
    conclusion_oracle_fixedhistogram_nearexhaustive_query_lowerbound_lowerBound candidateCount
        answerCount ≤ queryBudget := by
  classical
  have hexists : ∃ q, candidateCount ≤ answerCount ^ q := ⟨queryBudget, hIdentifies⟩
  rw [conclusion_oracle_fixedhistogram_nearexhaustive_query_lowerbound_lowerBound, dif_pos hexists]
  exact Nat.find_min' hexists hIdentifies

end Omega.Conclusion
