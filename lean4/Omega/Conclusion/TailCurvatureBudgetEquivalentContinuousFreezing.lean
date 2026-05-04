import Mathlib.Data.Real.Basic

namespace Omega.Conclusion

/-- The closed-form tail tent budget for the continuous freezing model. -/
noncomputable def conclusion_tail_curvature_budget_equivalent_continuous_freezing_eta
    (N : Nat) (t : Real) : Real :=
  if t <= (N : Real) - 2 then 0 else if t <= (N : Real) - 1 then t - ((N : Real) - 2) else 1

/-- Paper label: `thm:conclusion-tail-curvature-budget-equivalent-continuous-freezing`. -/
theorem paper_conclusion_tail_curvature_budget_equivalent_continuous_freezing (N : Nat)
    (_hN : 2 <= N) (t : Real) :
    conclusion_tail_curvature_budget_equivalent_continuous_freezing_eta N t =
      if t <= (N : Real) - 2 then 0
      else if t <= (N : Real) - 1 then t - ((N : Real) - 2)
      else 1 := by
  rfl

end Omega.Conclusion
