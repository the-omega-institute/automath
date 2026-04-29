import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete budget facts for
`cor:conclusion-circle-dimension-anomaly-rank-budget-splitting`. -/
structure conclusion_circle_dimension_anomaly_rank_budget_splitting_data where
  cdimStar : ℕ
  window6AbelianAnomalyRank : ℕ
  cdim_star_eq_one : cdimStar = 1
  window6_abelian_anomaly_rank_eq_twenty_one : window6AbelianAnomalyRank = 21
  finite_window_lie_factor_collapse_obstruction : cdimStar < window6AbelianAnomalyRank

def conclusion_circle_dimension_anomaly_rank_budget_splitting_statement
    (D : conclusion_circle_dimension_anomaly_rank_budget_splitting_data) : Prop :=
  D.cdimStar = 1 ∧
  D.window6AbelianAnomalyRank = 21 ∧
  D.cdimStar + D.window6AbelianAnomalyRank = 22 ∧
  D.cdimStar < D.window6AbelianAnomalyRank

/-- Paper label: `cor:conclusion-circle-dimension-anomaly-rank-budget-splitting`. -/
theorem paper_conclusion_circle_dimension_anomaly_rank_budget_splitting
    (D : conclusion_circle_dimension_anomaly_rank_budget_splitting_data) :
    conclusion_circle_dimension_anomaly_rank_budget_splitting_statement D := by
  have hsum : D.cdimStar + D.window6AbelianAnomalyRank = 22 := by
    rw [D.cdim_star_eq_one, D.window6_abelian_anomaly_rank_eq_twenty_one]
  exact ⟨D.cdim_star_eq_one, D.window6_abelian_anomaly_rank_eq_twenty_one, hsum,
    D.finite_window_lie_factor_collapse_obstruction⟩

end Omega.Conclusion
