namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-cycle-lattice-theta-tree-budget-lower-bound`. -/
theorem paper_conclusion_cycle_lattice_theta_tree_budget_lower_bound
    (poissonDuality hadamardTreeBudget optimizedTreeBudget equalityCriterion : Prop)
    (hDual : poissonDuality)
    (hHadamard : poissonDuality -> hadamardTreeBudget)
    (hOpt : hadamardTreeBudget -> optimizedTreeBudget)
    (hEq : optimizedTreeBudget -> equalityCriterion) :
    hadamardTreeBudget ∧ optimizedTreeBudget ∧ equalityCriterion := by
  have hHadamardBudget : hadamardTreeBudget := hHadamard hDual
  have hOptimizedBudget : optimizedTreeBudget := hOpt hHadamardBudget
  exact ⟨hHadamardBudget, hOptimizedBudget, hEq hOptimizedBudget⟩

end Omega.Conclusion
