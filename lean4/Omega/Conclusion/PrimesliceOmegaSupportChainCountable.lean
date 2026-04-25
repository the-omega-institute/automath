import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-primeslice-omega-support-chain-countable`. -/
theorem paper_conclusion_primeslice_omega_support_chain_countable :
    ∃ supportChain : ℕ → Finset ℕ,
      (∀ N, (supportChain N).card = N + 1) ∧
        (∀ N, supportChain N ⊂ supportChain (N + 1)) ∧
        ¬ ∃ S : Finset ℕ, ∀ N, supportChain N ⊆ S := by
  refine ⟨fun N => Finset.range (N + 1), ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro N
    simp
  · intro N
    refine ⟨?_, ?_⟩
    · intro x hx
      simp at hx ⊢
      omega
    · intro hNS
      have hmem : N + 1 ∈ Finset.range (N + 2) := by simp
      have : N + 1 ∈ Finset.range (N + 1) := hNS hmem
      simp at this
  · intro hS
    rcases hS with ⟨S, hS⟩
    have hcard_le : ∀ N, N + 1 ≤ S.card := by
      intro N
      have hsub := hS N
      simpa using Finset.card_le_card hsub
    have := hcard_le S.card
    omega

end Omega.Conclusion
