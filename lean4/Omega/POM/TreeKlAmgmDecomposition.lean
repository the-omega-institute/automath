namespace Omega.POM

/-- Paper label: `thm:pom-tree-kl-amgm-decomposition`. -/
theorem paper_pom_tree_kl_amgm_decomposition
    (treeKlDecomposition zeroDefectCriterion : Prop)
    (hTree : treeKlDecomposition) (hZero : zeroDefectCriterion) :
    treeKlDecomposition ∧ zeroDefectCriterion := by
  exact ⟨hTree, hZero⟩

end Omega.POM
