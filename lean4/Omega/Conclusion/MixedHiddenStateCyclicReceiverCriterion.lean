import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-mixed-hiddenstate-cyclic-receiver-criterion`. -/
theorem paper_conclusion_mixed_hiddenstate_cyclic_receiver_criterion (β N : ℕ)
    (FaithfulCyclicReceiver : ℕ → Prop)
    (hcriterion : ∀ m, FaithfulCyclicReceiver m ↔
      (β = 0 ∧ N ∣ m) ∨ (β = 1 ∧ Odd N ∧ 2 * N ∣ m)) :
    ((∃ m, FaithfulCyclicReceiver m) ↔ β = 0 ∨ (β = 1 ∧ Odd N)) ∧
      (β = 0 → FaithfulCyclicReceiver N) ∧
        (β = 1 → Odd N → FaithfulCyclicReceiver (2 * N)) ∧
          ((2 ≤ β ∨ (β = 1 ∧ Even N)) → ¬ ∃ m, FaithfulCyclicReceiver m) := by
  have hexists : (∃ m, FaithfulCyclicReceiver m) ↔ β = 0 ∨ (β = 1 ∧ Odd N) := by
    constructor
    · rintro ⟨m, hm⟩
      rcases (hcriterion m).mp hm with ⟨hβ, _⟩ | ⟨hβ, hodd, _⟩
      · exact Or.inl hβ
      · exact Or.inr ⟨hβ, hodd⟩
    · intro hβ
      rcases hβ with hβ | ⟨hβ, hodd⟩
      · refine ⟨N, (hcriterion N).mpr ?_⟩
        exact Or.inl ⟨hβ, dvd_rfl⟩
      · refine ⟨2 * N, (hcriterion (2 * N)).mpr ?_⟩
        exact Or.inr ⟨hβ, hodd, dvd_rfl⟩
  refine ⟨hexists, ?_, ?_, ?_⟩
  · intro hβ
    exact (hcriterion N).mpr (Or.inl ⟨hβ, dvd_rfl⟩)
  · intro hβ hodd
    exact (hcriterion (2 * N)).mpr (Or.inr ⟨hβ, hodd, dvd_rfl⟩)
  · intro hforbidden hcycle
    rcases hforbidden with hβge | ⟨hβone, heven⟩
    · rcases hexists.mp hcycle with hβzero | ⟨hβone, _⟩
      · omega
      · omega
    · rcases hexists.mp hcycle with hβzero | ⟨_, hodd⟩
      · omega
      · exact (Nat.not_even_iff_odd.mpr hodd) heven

end Omega.Conclusion
