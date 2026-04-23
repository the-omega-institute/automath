import Mathlib.Tactic
import Omega.Conclusion.SingleOmittedEdgePartialCorrelationBudget

namespace Omega.Conclusion

/-- Concrete threshold data for uniform omitted-edge control in the tree-approximation proxy. The
record stores the per-tree partial correlation, the nonnegative slack coming from the rest of the
tree, and a single threshold dominating every scalar proxy budget. -/
structure conclusion_tree_approximation_uniform_threshold_certificate_data where
  Tree : Type
  partialCorrelation : Tree → ℝ
  treeSlack : Tree → ℝ
  threshold : ℝ
  slack_nonneg : ∀ T, 0 ≤ treeSlack T
  threshold_dominates_budget :
    ∀ T,
      Real.sqrt
          (2 *
            conclusion_fundamental_cycle_cmi_dominated_by_global_tree_entropy_tree_defect
              (partialCorrelation T) (treeSlack T)) ≤
        threshold

/-- Every omitted-edge partial correlation is uniformly bounded by the common threshold. -/
def conclusion_tree_approximation_uniform_threshold_certificate_statement
    (D : conclusion_tree_approximation_uniform_threshold_certificate_data) : Prop :=
  ∀ T, |D.partialCorrelation T| ≤ D.threshold

/-- Paper label: `cor:conclusion-tree-approximation-uniform-threshold-certificate`. The scalar
omitted-edge proxy gives a per-tree partial-correlation bound, and the hypothesis that one common
threshold dominates all those budgets upgrades it to a uniform certificate. -/
theorem paper_conclusion_tree_approximation_uniform_threshold_certificate
    (D : conclusion_tree_approximation_uniform_threshold_certificate_data) :
    conclusion_tree_approximation_uniform_threshold_certificate_statement D := by
  intro T
  have hScalar :=
    paper_conclusion_single_omitted_edge_partial_correlation_budget
      (D.partialCorrelation T) (D.treeSlack T) (D.slack_nonneg T)
  exact le_trans hScalar.2 (D.threshold_dominates_budget T)

end Omega.Conclusion
