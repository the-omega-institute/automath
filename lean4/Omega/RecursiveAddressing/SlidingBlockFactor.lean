import Mathlib.Tactic

namespace Omega.RecursiveAddressing.SlidingBlockFactor

/-- The one-sided sliding-block code induced by local window rules. -/
def slidingBlockCode
    {β : Type} {r w : ℕ}
    (rules : Fin r → (Fin w → β) → Bool) (y : ℕ → β) :
    ℕ → Fin r → Bool :=
  fun t j => rules j (fun i => y (t + i.val))

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: each recursive step factors through a one-sided sliding-block code with the
given local cylinder rules.
    prop:sliding-block-factor -/
theorem paper_scan_projection_address_sliding_block_factor_seeds
    {X β : Type} {rNext w : ℕ}
    (rules : Fin rNext → (Fin w → β) → Bool)
    (πL : X → ℕ → β)
    (πNext : X → ℕ → Fin rNext → Bool)
    (hπ : ∀ x t j, πNext x t j = rules j (fun i => πL x (t + i.val))) :
    ∃ Φ : (ℕ → β) → ℕ → Fin rNext → Bool,
      (∀ y t j, Φ y t j = rules j (fun i => y (t + i.val))) ∧
      ∀ x, πNext x = Φ (πL x) := by
  refine ⟨slidingBlockCode rules, ?_, ?_⟩
  · intro y t j
    rfl
  · intro x
    funext t j
    exact hπ x t j

/-- Wrapper theorem matching the ETDS publication label.
    prop:sliding-block-factor -/
theorem paper_scan_projection_address_sliding_block_factor_package
    {X β : Type} {rNext w : ℕ}
    (rules : Fin rNext → (Fin w → β) → Bool)
    (πL : X → ℕ → β)
    (πNext : X → ℕ → Fin rNext → Bool)
    (hπ : ∀ x t j, πNext x t j = rules j (fun i => πL x (t + i.val))) :
    ∃ Φ : (ℕ → β) → ℕ → Fin rNext → Bool,
      (∀ y t j, Φ y t j = rules j (fun i => y (t + i.val))) ∧
      ∀ x, πNext x = Φ (πL x) :=
  paper_scan_projection_address_sliding_block_factor_seeds rules πL πNext hπ

end Omega.RecursiveAddressing.SlidingBlockFactor
