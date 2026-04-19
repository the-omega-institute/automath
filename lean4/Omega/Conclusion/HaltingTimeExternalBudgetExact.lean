import Mathlib.Tactic

namespace Omega.Conclusion

/-- Chapter-local package for the exact external-budget computation of the time-indexed halting
encoding. The fields record whether the machine halts, the halting time when it does, the external
budget of the constructed encoding, and the exact formulas in the halting and non-halting cases. -/
structure HaltingTimeExternalBudgetExactData where
  halts : Prop
  haltingSteps : ℕ
  externalBudget : ℕ
  nonhalting_budget : ¬ halts → externalBudget = 1
  halting_budget : halts → externalBudget = haltingSteps + 1

/-- Paper-facing exact budget formula for the halting-time externalization.
    thm:conclusion-halting-time-external-budget-exact -/
theorem paper_conclusion_halting_time_external_budget_exact
    (h : HaltingTimeExternalBudgetExactData) :
    (¬ h.halts → h.externalBudget = 1) ∧
      (h.halts → h.externalBudget = h.haltingSteps + 1) := by
  exact ⟨h.nonhalting_budget, h.halting_budget⟩

end Omega.Conclusion
