import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-resonance-window-infinitely-many-fully-auditable-primes`. -/
theorem paper_conclusion_resonance_window_infinitely_many_fully_auditable_primes
    (Prime Good badRank badT badDisc : ℕ → Prop)
    (hFiniteBad :
      ∃ bads : Finset ℕ, ∀ p : ℕ, badRank p ∨ badT p ∨ badDisc p → p ∈ bads)
    (hEuclid : ∀ S : Finset ℕ, ∃ p : ℕ, Prime p ∧ p ∉ S)
    (hGood :
      ∀ p : ℕ, Prime p → ¬ (badRank p ∨ badT p ∨ badDisc p) → Good p) :
    ∀ S : Finset ℕ, ∃ p : ℕ, Good p ∧ p ∉ S := by
  rcases hFiniteBad with ⟨bads, hBads⟩
  intro S
  rcases hEuclid (S ∪ bads) with ⟨p, hpPrime, hpAvoid⟩
  refine ⟨p, ?_, ?_⟩
  · exact hGood p hpPrime fun hpBad =>
      hpAvoid (Finset.mem_union.mpr (Or.inr (hBads p hpBad)))
  · intro hpS
    exact hpAvoid (Finset.mem_union.mpr (Or.inl hpS))

end Omega.Conclusion
