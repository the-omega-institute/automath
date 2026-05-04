import Mathlib.Tactic
import Omega.Conclusion.MinimalExternalBudgetUndecidable
import Omega.Conclusion.MinimalStateComplexityHalting

namespace Omega.Conclusion

/-- Concrete data for extracting a Busy-Beaver lower bound from the halting-state-complexity
package while retaining a two-fiber external-budget certificate. -/
structure conclusion_bounded_fiber_unbounded_state_busybeaver_data where
  conclusion_bounded_fiber_unbounded_state_busybeaver_statePackage :
    ConclusionMinimalStateComplexityHaltingData
  conclusion_bounded_fiber_unbounded_state_busybeaver_busyBeaverValue : ℕ
  conclusion_bounded_fiber_unbounded_state_busybeaver_minimalExternalBudget : ℕ
  conclusion_bounded_fiber_unbounded_state_busybeaver_halts :
    conclusion_bounded_fiber_unbounded_state_busybeaver_statePackage.halts
  conclusion_bounded_fiber_unbounded_state_busybeaver_busyBeaver_attained :
    conclusion_bounded_fiber_unbounded_state_busybeaver_busyBeaverValue ≤
      conclusion_bounded_fiber_unbounded_state_busybeaver_statePackage.haltingSteps
  conclusion_bounded_fiber_unbounded_state_busybeaver_budget_le_two :
    conclusion_bounded_fiber_unbounded_state_busybeaver_minimalExternalBudget ≤ 2

/-- A bounded external budget coexists with a state-count lower bound at the Busy-Beaver scale. -/
def conclusion_bounded_fiber_unbounded_state_busybeaver_statement
    (D : conclusion_bounded_fiber_unbounded_state_busybeaver_data) : Prop :=
  conclusion_minimal_external_budget_undecidable_statement ∧
    D.conclusion_bounded_fiber_unbounded_state_busybeaver_minimalExternalBudget ≤ 2 ∧
      D.conclusion_bounded_fiber_unbounded_state_busybeaver_busyBeaverValue + 1 ≤
        D.conclusion_bounded_fiber_unbounded_state_busybeaver_statePackage.minStateCount

/-- Paper label: `cor:conclusion-bounded-fiber-unbounded-state-busybeaver`. -/
theorem paper_conclusion_bounded_fiber_unbounded_state_busybeaver
    (D : conclusion_bounded_fiber_unbounded_state_busybeaver_data) :
    conclusion_bounded_fiber_unbounded_state_busybeaver_statement D := by
  unfold conclusion_bounded_fiber_unbounded_state_busybeaver_statement
  refine ⟨paper_conclusion_minimal_external_budget_undecidable,
    D.conclusion_bounded_fiber_unbounded_state_busybeaver_budget_le_two, ?_⟩
  have hstate :=
    (paper_conclusion_minimal_state_complexity_halting
      D.conclusion_bounded_fiber_unbounded_state_busybeaver_statePackage).1
        D.conclusion_bounded_fiber_unbounded_state_busybeaver_halts
  rw [hstate]
  exact Nat.succ_le_succ
    D.conclusion_bounded_fiber_unbounded_state_busybeaver_busyBeaver_attained

end Omega.Conclusion
