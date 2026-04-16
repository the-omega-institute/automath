import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- Chapter-local wrapper for the orthogonal readout budgets in typed-address biaxial completion.
It packages the necessity of the visible/register/mode budgets for a legal readout together with
the non-substitutability of each axis when the other two succeed. -/
structure BudgetOrthogonalityData where
  legalReadout : Prop
  visibleBudgetPassed : Prop
  registerBudgetPassed : Prop
  modeBudgetPassed : Prop
  visible_required : legalReadout → visibleBudgetPassed
  register_required : legalReadout → registerBudgetPassed
  mode_required : legalReadout → modeBudgetPassed
  visible_failure_obstructs :
    registerBudgetPassed → modeBudgetPassed → ¬ visibleBudgetPassed → ¬ legalReadout
  register_failure_obstructs :
    visibleBudgetPassed → modeBudgetPassed → ¬ registerBudgetPassed → ¬ legalReadout
  mode_failure_obstructs :
    visibleBudgetPassed → registerBudgetPassed → ¬ modeBudgetPassed → ¬ legalReadout

/-- Legal typed-address readout is orthogonal in the visible/register/mode budgets: it forces all
three budgets to pass, and failure of any single axis cannot be compensated by the other two.
    prop:typed-address-biaxial-completion-budget-orthogonality -/
theorem paper_typed_address_biaxial_completion_budget_orthogonality
    (h : BudgetOrthogonalityData) :
    (h.legalReadout → h.visibleBudgetPassed ∧ h.registerBudgetPassed ∧ h.modeBudgetPassed) ∧
      ((h.registerBudgetPassed ∧ h.modeBudgetPassed ∧ ¬ h.visibleBudgetPassed) →
        ¬ h.legalReadout) ∧
      ((h.visibleBudgetPassed ∧ h.modeBudgetPassed ∧ ¬ h.registerBudgetPassed) →
        ¬ h.legalReadout) ∧
      ((h.visibleBudgetPassed ∧ h.registerBudgetPassed ∧ ¬ h.modeBudgetPassed) →
        ¬ h.legalReadout) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hlegal
    exact ⟨h.visible_required hlegal, h.register_required hlegal, h.mode_required hlegal⟩
  · rintro ⟨hregister, hmode, hvisible⟩
    exact h.visible_failure_obstructs hregister hmode hvisible
  · rintro ⟨hvisible, hmode, hregister⟩
    exact h.register_failure_obstructs hvisible hmode hregister
  · rintro ⟨hvisible, hregister, hmode⟩
    exact h.mode_failure_obstructs hvisible hregister hmode

end Omega.TypedAddressBiaxialCompletion
