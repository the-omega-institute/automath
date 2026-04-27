import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-mixed-hidden-state-minimal-finite-receiver`. Any
injective receiver embedding must have at least as many finite states as the hidden state. -/
theorem paper_conclusion_mixed_hidden_state_minimal_finite_receiver {H G : Type*}
    [Fintype H] [Fintype G] (β N : Nat) (hH : Fintype.card H = 2 ^ β * N)
    (f : H → G) (hf : Function.Injective f) :
    2 ^ β * N ≤ Fintype.card G := by
  rw [← hH]
  exact Fintype.card_le_of_injective f hf

end Omega.Conclusion
