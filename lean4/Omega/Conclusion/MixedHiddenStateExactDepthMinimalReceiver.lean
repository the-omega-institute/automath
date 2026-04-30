import Mathlib.Data.Fintype.Card

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-mixed-hidden-state-exact-depth-minimal-receiver`. -/
theorem paper_conclusion_mixed_hidden_state_exact_depth_minimal_receiver
    (β Fd : Nat) {H G : Type*} [Fintype H] [Fintype G]
    (hH : Fintype.card H = 2 ^ β * Fd) (f : H → G) (hf : Function.Injective f) :
    2 ^ β * Fd ≤ Fintype.card G := by
  rw [← hH]
  exact Fintype.card_le_of_injective f hf

end Omega.Conclusion
