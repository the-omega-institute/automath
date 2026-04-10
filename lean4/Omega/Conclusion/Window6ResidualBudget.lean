import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Conclusion.Window6Collision

namespace Omega.Conclusion

/-- Paper: `cor:conclusion-window6-minimal-faithful-residual-budget-18`. -/
theorem paper_conclusion_window6_minimal_faithful_residual_budget_18
    (r : Nat) (hinj : Fin 18 ↪ Fin r) :
    18 ≤ r := by
  have hcard := Fintype.card_le_of_embedding hinj
  simpa [Fintype.card_fin] using hcard

end Omega.Conclusion
