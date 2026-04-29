import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-chain-idempotent-comparability-bidirectional-defect`. -/
theorem paper_xi_chain_idempotent_comparability_bidirectional_defect {α : Type*} [DecidableEq α]
    (Δ : Finset α → Finset α → ℕ) (hΔ : ∀ F G, Δ F G = 0 ↔ G ⊆ F) (F G : Finset α) :
    ((F ⊆ G ∨ G ⊆ F) ↔ Δ F G * Δ G F = 0) := by
  constructor
  · rintro (hFG | hGF)
    · have hzero : Δ G F = 0 := (hΔ G F).2 hFG
      simp [hzero]
    · have hzero : Δ F G = 0 := (hΔ F G).2 hGF
      simp [hzero]
  · intro hprod
    rcases Nat.mul_eq_zero.mp hprod with hFGzero | hGFzero
    · exact Or.inr ((hΔ F G).1 hFGzero)
    · exact Or.inl ((hΔ G F).1 hGFzero)

end Omega.Zeta
