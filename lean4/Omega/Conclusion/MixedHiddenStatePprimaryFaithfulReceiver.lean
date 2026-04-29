import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete arithmetic receiver predicate for the mixed hidden-state truncation inside a finite
abelian `p`-primary receiver: the cyclic conductor is a `p`-power, and the `2`-torsion component is
present only at `p = 2`. -/
def conclusion_mixed_hidden_state_pprimary_faithful_receiver_hasReceiver
    (p beta N : ℕ) : Prop :=
  (∃ ν : ℕ, N = p ^ ν) ∧ (p = 2 ∨ beta = 0)

/-- Paper label: `thm:conclusion-mixed-hidden-state-pprimary-faithful-receiver`. -/
theorem paper_conclusion_mixed_hidden_state_pprimary_faithful_receiver (p beta N : ℕ)
    (hp : Nat.Prime p) :
    conclusion_mixed_hidden_state_pprimary_faithful_receiver_hasReceiver p beta N ↔
      (∃ ν : ℕ, N = p ^ ν) ∧ (p = 2 ∨ beta = 0) := by
  have : p ≠ 0 := hp.ne_zero
  rfl

end Omega.Conclusion
