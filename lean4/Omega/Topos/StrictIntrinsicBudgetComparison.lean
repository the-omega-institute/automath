import Omega.Topos.StrictToIntrinsicVisible

namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for comparing the intrinsic hidden-state budget
    with the strict presentation-level budget.
    cor:strict-intrinsic-budget-comparison -/
theorem paper_conservative_extension_strict_intrinsic_budget_comparison
    (strictVisible budgetInequality quotientIsomorphism : Prop)
    (hVisible : strictVisible)
    (hBudget : strictVisible → budgetInequality)
    (hIso : strictVisible → quotientIsomorphism) :
    budgetInequality ∧ quotientIsomorphism := by
  exact ⟨hBudget hVisible, hIso hVisible⟩

end Omega.Topos
