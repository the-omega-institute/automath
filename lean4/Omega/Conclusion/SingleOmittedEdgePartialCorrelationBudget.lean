import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Omega.Conclusion.FundamentalCycleCmiDominatedByGlobalTreeEntropy

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-single-omitted-edge-partial-correlation-budget`. The omitted-edge
CMI is exactly the quadratic partial-correlation term, and the global tree-entropy defect bounds
that term; taking square roots yields the absolute-value control. -/
theorem paper_conclusion_single_omitted_edge_partial_correlation_budget
    (ρ treeSlack : ℝ) (hSlack : 0 ≤ treeSlack) :
    ρ ^ 2 ≤
        2 * conclusion_fundamental_cycle_cmi_dominated_by_global_tree_entropy_tree_defect
          ρ treeSlack ∧
      |ρ| ≤ Real.sqrt
        (2 * conclusion_fundamental_cycle_cmi_dominated_by_global_tree_entropy_tree_defect
          ρ treeSlack) := by
  rcases
      paper_conclusion_fundamental_cycle_cmi_dominated_by_global_tree_entropy ρ treeSlack hSlack with
    ⟨hEq, hLe⟩
  have hLe' :
      conclusion_fundamental_cycle_cmi_dominated_by_global_tree_entropy_partial_correlation ρ ≤
        conclusion_fundamental_cycle_cmi_dominated_by_global_tree_entropy_tree_defect
          ρ treeSlack := by
    rw [← hEq]
    exact hLe
  have hFirst :
      ρ ^ 2 ≤
        2 * conclusion_fundamental_cycle_cmi_dominated_by_global_tree_entropy_tree_defect
          ρ treeSlack := by
    unfold conclusion_fundamental_cycle_cmi_dominated_by_global_tree_entropy_partial_correlation
      at hLe'
    nlinarith
  have hSecond :
      |ρ| ≤
        Real.sqrt
          (2 * conclusion_fundamental_cycle_cmi_dominated_by_global_tree_entropy_tree_defect
            ρ treeSlack) := by
    exact Real.abs_le_sqrt hFirst
  exact ⟨hFirst, hSecond⟩

end Omega.Conclusion
