import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-fibadic-cyclic-receiver-thin-exceptional-sector`. -/
theorem paper_conclusion_fibadic_cyclic_receiver_thin_exceptional_sector
    (β N : ℕ) (FaithfulCyclicReceiver : ℕ → Prop)
    (hcriterion :
      (∃ M : ℕ, FaithfulCyclicReceiver M) ↔
        β = 0 ∨ (β = 1 ∧ ∃ t : ℕ, N = 2 * t + 1)) :
    ((∃ M : ℕ, FaithfulCyclicReceiver M) ↔
        β = 0 ∨ (β = 1 ∧ ∃ t : ℕ, N = 2 * t + 1)) ∧
      ((2 ≤ β ∨ (β = 1 ∧ ∃ t : ℕ, N = 2 * t)) →
        ¬ ∃ M : ℕ, FaithfulCyclicReceiver M) := by
  refine ⟨hcriterion, ?_⟩
  intro hbad hreceiver
  have hallowed :
      β = 0 ∨ (β = 1 ∧ ∃ t : ℕ, N = 2 * t + 1) :=
    hcriterion.mp hreceiver
  rcases hbad with htwo | hEven
  · rcases hallowed with hzero | hone
    · omega
    · rcases hone with ⟨hone, _⟩
      omega
  · rcases hEven with ⟨hβ, t, ht⟩
    rcases hallowed with hzero | hOdd
    · omega
    · rcases hOdd with ⟨_, u, hu⟩
      omega

end Omega.Conclusion
