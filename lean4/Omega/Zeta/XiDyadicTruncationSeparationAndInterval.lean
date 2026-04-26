namespace Omega.Zeta

/-- Paper label: `thm:xi-dyadic-truncation-separation-and-interval`. -/
theorem paper_xi_dyadic_truncation_separation_and_interval
    (aliasErrorBound truncationErrorBound intervalCriterion : Prop)
    (hSep : aliasErrorBound → truncationErrorBound → intervalCriterion) :
    aliasErrorBound → truncationErrorBound → intervalCriterion := by
  intro hAlias hTrunc
  exact hSep hAlias hTrunc

end Omega.Zeta
