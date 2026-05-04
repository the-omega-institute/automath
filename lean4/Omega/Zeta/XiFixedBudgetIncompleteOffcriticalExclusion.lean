/-- Paper label: `cor:xi-fixed-budget-incomplete-offcritical-exclusion`. -/
theorem paper_xi_fixed_budget_incomplete_offcritical_exclusion {Height : Type}
    (heightLe : Height → Height → Prop) (radiusBlind addressCollision : Height → Prop)
    (hEventually :
      ∃ T0, ∀ T, heightLe T0 T → radiusBlind T ∨ addressCollision T) :
    ∃ T0, ∀ T, heightLe T0 T → radiusBlind T ∨ addressCollision T := by
  exact hEventually
