import Mathlib.Tactic

namespace Omega.Conclusion

open Finset

/-- Paper label: `cor:conclusion-zero-rate-endpoint-first-order-blind-hyperplane`. -/
theorem paper_conclusion_zero_rate_endpoint_first_order_blind_hyperplane {X : Type*}
    [Fintype X] (w dw : X → ℝ) (h0 : (∑ x, dw x) = 0)
    (h1 : (∑ x, dw x * w x) = 0) :
    dw ∈ {v : X → ℝ | (∑ x, v x) = 0 ∧ (∑ x, v x * w x) = 0} := by
  exact ⟨h0, h1⟩

end Omega.Conclusion
