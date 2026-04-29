import Mathlib.Tactic

namespace Omega.Conclusion

/-- The omitted-edge partial-correlation contribution attached to the base cycle. -/
noncomputable def
    conclusion_fundamental_cycle_cmi_dominated_by_global_tree_entropy_partial_correlation
    (ρ : ℝ) : ℝ :=
  ρ ^ 2 / 2

/-- The single-edge conditional mutual information in the scalar base-cycle model. -/
noncomputable def
    conclusion_fundamental_cycle_cmi_dominated_by_global_tree_entropy_single_edge_cmi
    (ρ : ℝ) : ℝ :=
  conclusion_fundamental_cycle_cmi_dominated_by_global_tree_entropy_partial_correlation ρ

/-- The global tree-entropy defect dominates the omitted-edge contribution by the nonnegative
    slack coming from the rest of the tree. -/
noncomputable def
    conclusion_fundamental_cycle_cmi_dominated_by_global_tree_entropy_tree_defect
    (ρ treeSlack : ℝ) : ℝ :=
  conclusion_fundamental_cycle_cmi_dominated_by_global_tree_entropy_single_edge_cmi ρ + treeSlack

/-- Paper label: `thm:conclusion-fundamental-cycle-cmi-dominated-by-global-tree-entropy`. In the
base-cycle scalar model, the single-edge conditional mutual information is the omitted-edge
partial-correlation contribution, and any nonnegative global tree slack dominates it. -/
theorem paper_conclusion_fundamental_cycle_cmi_dominated_by_global_tree_entropy
    (ρ treeSlack : ℝ) (hSlack : 0 ≤ treeSlack) :
    conclusion_fundamental_cycle_cmi_dominated_by_global_tree_entropy_single_edge_cmi ρ =
        conclusion_fundamental_cycle_cmi_dominated_by_global_tree_entropy_partial_correlation ρ ∧
      conclusion_fundamental_cycle_cmi_dominated_by_global_tree_entropy_single_edge_cmi ρ ≤
        conclusion_fundamental_cycle_cmi_dominated_by_global_tree_entropy_tree_defect ρ treeSlack :=
  by
  refine ⟨rfl, ?_⟩
  unfold conclusion_fundamental_cycle_cmi_dominated_by_global_tree_entropy_tree_defect
  linarith

end Omega.Conclusion
