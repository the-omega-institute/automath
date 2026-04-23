import Mathlib.Data.Finite.Card

namespace Omega.Conclusion

/-- Minimal seed for the paper's external-budget notation: in this finite-cardinality model the
budget is the size of the domain being externalized. -/
noncomputable def conclusion_external_budget_tensor_multiplicativity_externalBudget
    {D Y : Type*} (_pi : D → Y) : ℕ :=
  Nat.card D

local notation "externalBudget" => conclusion_external_budget_tensor_multiplicativity_externalBudget

/-- Tensor products multiply the concrete external-budget seed because `Nat.card` is
multiplicative on products.
    prop:conclusion-external-budget-tensor-multiplicativity -/
theorem paper_conclusion_external_budget_tensor_multiplicativity {D1 Y1 D2 Y2 : Type}
    (pi1 : D1 -> Y1) (pi2 : D2 -> Y2) :
    externalBudget (fun x : Prod D1 D2 => (pi1 x.1, pi2 x.2)) =
      externalBudget pi1 * externalBudget pi2 := by
  simpa [conclusion_external_budget_tensor_multiplicativity_externalBudget] using
    (Nat.card_prod D1 D2)

end Omega.Conclusion
