import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-equivariant-binary-jump-ledger-lower-bound`. -/
theorem paper_xi_equivariant_binary_jump_ledger_lower_bound {Ω : Type*} [Fintype Ω]
    [DecidableEq Ω] (b : ℕ) (orbit : Finset Ω) (Φ : Fin (2 ^ b) → Ω)
    (hcover : ∀ ω, ω ∈ orbit → ∃ B : Fin (2 ^ b), Φ B = ω) : orbit.card ≤ 2 ^ b := by
  classical
  have hsubset : orbit ⊆ (Finset.univ.image Φ : Finset Ω) := by
    intro ω hω
    rcases hcover ω hω with ⟨B, hB⟩
    exact Finset.mem_image.mpr ⟨B, by simp, hB⟩
  calc
    orbit.card ≤ (Finset.univ.image Φ : Finset Ω).card := Finset.card_le_card hsubset
    _ ≤ (Finset.univ : Finset (Fin (2 ^ b))).card := Finset.card_image_le
    _ = 2 ^ b := by simp

end Omega.Zeta
