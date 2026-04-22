import Omega.TypedAddressBiaxialCompletion.BudgetOrthogonality

namespace Omega.UnitCirclePhaseArithmetic

/-- Chapter-local complete-phase wrapper for the three threshold predicates transported from the
typed-address budget orthogonality package. -/
def UnitCircleCompletePhaseThresholdOrthogonalityStatement : Prop :=
  ∀ h : Omega.TypedAddressBiaxialCompletion.BudgetOrthogonalityData,
    (h.legalReadout → h.visibleBudgetPassed ∧ h.registerBudgetPassed ∧ h.modeBudgetPassed) ∧
      ((h.registerBudgetPassed ∧ h.modeBudgetPassed ∧ ¬ h.visibleBudgetPassed) →
        ¬ h.legalReadout) ∧
      ((h.visibleBudgetPassed ∧ h.modeBudgetPassed ∧ ¬ h.registerBudgetPassed) →
        ¬ h.legalReadout) ∧
      ((h.visibleBudgetPassed ∧ h.registerBudgetPassed ∧ ¬ h.modeBudgetPassed) →
        ¬ h.legalReadout)

/-- Paper label: `prop:unit-circle-complete-phase-threshold-orthogonality`. -/
theorem paper_unit_circle_complete_phase_threshold_orthogonality :
    UnitCircleCompletePhaseThresholdOrthogonalityStatement := by
  intro h
  exact Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_budget_orthogonality h

end Omega.UnitCirclePhaseArithmetic
