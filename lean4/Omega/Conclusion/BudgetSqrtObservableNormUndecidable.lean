import Mathlib.Tactic

namespace Omega.Conclusion

set_option maxHeartbeats 400000 in
/-- If the sqrt-two observable-norm problem is equivalent to the budget-one problem, then any
    decision procedure for the former would decide the latter.
    cor:conclusion-budget-sqrt-observable-norm-undecidable -/
theorem paper_conclusion_budget_sqrt_observable_norm_undecidable
    (observableNormIsSqrtTwo budgetOne : Prop) :
    (observableNormIsSqrtTwo <-> budgetOne) ->
      (¬ Nonempty (Decidable budgetOne)) ->
      ¬ Nonempty (Decidable observableNormIsSqrtTwo) := by
  intro hEquiv hUndecidable hDecidable
  rcases hDecidable with ⟨hDecidableSqrtTwo⟩
  letI : Decidable observableNormIsSqrtTwo := hDecidableSqrtTwo
  apply hUndecidable
  exact ⟨decidable_of_iff observableNormIsSqrtTwo hEquiv⟩

end Omega.Conclusion
