namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-fibadic-old-algebra-exact-conductor-qd`. -/
theorem paper_conclusion_fibadic_old_algebra_exact_conductor_qd
    (ExactOldAlgebra ExactConductor DimensionFormula PropernessCriterion : Prop)
    (hOld : ExactOldAlgebra) (hCond : ExactConductor) (hDim : DimensionFormula)
    (hProper : PropernessCriterion) :
    ExactOldAlgebra ∧ ExactConductor ∧ DimensionFormula ∧ PropernessCriterion := by
  exact ⟨hOld, hCond, hDim, hProper⟩

end Omega.Conclusion
