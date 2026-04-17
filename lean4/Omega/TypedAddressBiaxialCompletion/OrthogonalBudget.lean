import Omega.TypedAddressBiaxialCompletion.OrthogonalSlice

namespace Omega.TypedAddressBiaxialCompletion

/-- The three typed-address biaxial-completion budgets are non-compensating when failure on any
single axis already blocks legal readout despite the other two axes passing. -/
def typedAddressBiaxialCompletionOrthogonalBudget
    (legalReadout visibleBudgetPassed registerBudgetPassed modeBudgetPassed : Prop) : Prop :=
  ((registerBudgetPassed ∧ modeBudgetPassed ∧ ¬ visibleBudgetPassed) → ¬ legalReadout) ∧
    ((visibleBudgetPassed ∧ modeBudgetPassed ∧ ¬ registerBudgetPassed) → ¬ legalReadout) ∧
    ((visibleBudgetPassed ∧ registerBudgetPassed ∧ ¬ modeBudgetPassed) → ¬ legalReadout)

/-- Packaging of the orthogonal-slice theorem: once legal readout forces the visible, register,
and mode budgets simultaneously, the three axes cannot compensate for one another.
    cor:typed-address-biaxial-completion-orthogonal-budget -/
theorem paper_typed_address_biaxial_completion_orthogonal_budget
    (legalReadout visibleBudgetPassed registerBudgetPassed modeBudgetPassed : Prop)
    (hVisibleRequired : legalReadout → visibleBudgetPassed)
    (hRegisterRequired : legalReadout → registerBudgetPassed)
    (hModeRequired : legalReadout → modeBudgetPassed)
    (hVisibleFailure :
      registerBudgetPassed → modeBudgetPassed → ¬ visibleBudgetPassed → ¬ legalReadout)
    (hRegisterFailure :
      visibleBudgetPassed → modeBudgetPassed → ¬ registerBudgetPassed → ¬ legalReadout)
    (hModeFailure :
      visibleBudgetPassed → registerBudgetPassed → ¬ modeBudgetPassed → ¬ legalReadout) :
    typedAddressBiaxialCompletionOrthogonalBudget legalReadout visibleBudgetPassed
      registerBudgetPassed modeBudgetPassed := by
  let U : UnitarySliceAddressClosureData :=
    { AddressSpace := Unit
      ReadoutCodomain := Unit
      unitarySliceAddress := fun _ => True
      guardedReadout := fun _ _ => ()
      guardedRule := True
      readUSClosed := True
      hasGuardedRule := trivial
      guardedReadoutCloses := fun _ => trivial }
  let B : BudgetOrthogonalityData :=
    { legalReadout := legalReadout
      visibleBudgetPassed := visibleBudgetPassed
      registerBudgetPassed := registerBudgetPassed
      modeBudgetPassed := modeBudgetPassed
      visible_required := hVisibleRequired
      register_required := hRegisterRequired
      mode_required := hModeRequired
      visible_failure_obstructs := hVisibleFailure
      register_failure_obstructs := hRegisterFailure
      mode_failure_obstructs := hModeFailure }
  let N : TypedAddressNullTrichotomyData :=
    { semanticNullCause := True
      protocolNullCause := True
      collisionNullCause := True
      exhaustive := True
      semanticFailuresRequireAddressChange := True
      protocolFailuresNeedProtocolRepair := True
      collisionFailuresNeedSupportAxisBudget := True
      exhaustiveWitness := trivial
      semanticRepairWitness := trivial
      protocolRepairWitness := trivial
      collisionRepairWitness := trivial }
  have hSlice := paper_typed_address_biaxial_completion_orthogonal_slice U B N
  have hAllBudgets : legalReadout →
      visibleBudgetPassed ∧ registerBudgetPassed ∧ modeBudgetPassed := hSlice.2.1
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hRegister, hMode, hNotVisible⟩ hLegal
    exact hNotVisible (hAllBudgets hLegal).1
  · rintro ⟨hVisible, hMode, hNotRegister⟩ hLegal
    exact hNotRegister (hAllBudgets hLegal).2.1
  · rintro ⟨hVisible, hRegister, hNotMode⟩ hLegal
    exact hNotMode (hAllBudgets hLegal).2.2

end Omega.TypedAddressBiaxialCompletion
