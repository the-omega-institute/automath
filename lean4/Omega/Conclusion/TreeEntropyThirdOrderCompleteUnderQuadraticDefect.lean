namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-tree-entropy-third-order-complete-under-quadratic-defect`. -/
theorem paper_conclusion_tree_entropy_third_order_complete_under_quadratic_defect
    (quadraticDefect loopFourthOrder treeThirdOrderComplete : Prop)
    (hquad : quadraticDefect -> loopFourthOrder)
    (hadd : loopFourthOrder -> treeThirdOrderComplete) :
    quadraticDefect -> treeThirdOrderComplete := by
  intro hDefect
  exact hadd (hquad hDefect)

end Omega.Conclusion
