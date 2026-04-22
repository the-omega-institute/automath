import Omega.TypedAddressBiaxialCompletion.BudgetOrthogonality

namespace Omega.UnitCirclePhaseArithmetic

/-- Paper label: `prop:unit-circle-complete-phase-budget-orthogonal`. -/
theorem paper_unit_circle_complete_phase_budget_orthogonal
    (h : Omega.TypedAddressBiaxialCompletion.BudgetOrthogonalityData) :
    (h.legalReadout → h.visibleBudgetPassed ∧ h.registerBudgetPassed ∧ h.modeBudgetPassed) ∧
      ((h.registerBudgetPassed ∧ h.modeBudgetPassed ∧ ¬ h.visibleBudgetPassed) →
        ¬ h.legalReadout) ∧
      ((h.visibleBudgetPassed ∧ h.modeBudgetPassed ∧ ¬ h.registerBudgetPassed) →
        ¬ h.legalReadout) ∧
      ((h.visibleBudgetPassed ∧ h.registerBudgetPassed ∧ ¬ h.modeBudgetPassed) →
        ¬ h.legalReadout) := by
  exact Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_budget_orthogonality h

end Omega.UnitCirclePhaseArithmetic
