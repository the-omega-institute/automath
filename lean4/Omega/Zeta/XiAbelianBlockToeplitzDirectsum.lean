import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-abelian-block-toeplitz-directsum`. -/
theorem paper_xi_abelian_block_toeplitz_directsum
    {Block Channel : Type} (Tblock : ℕ → Block) (Tchan : Channel → ℕ → Block)
    (PSD : Block → Prop) (unitarilyEquivalent : Block → Block → Prop)
    (directSum : (Channel → Block) → Block)
    (hdiag : ∀ N, unitarilyEquivalent (Tblock N) (directSum (fun χ => Tchan χ N)))
    (hPSD_equiv : ∀ A B, unitarilyEquivalent A B → (PSD A ↔ PSD B))
    (hPSD_directSum : ∀ f, PSD (directSum f) ↔ ∀ χ, PSD (f χ)) :
    ∀ N, PSD (Tblock N) ↔ ∀ χ, PSD (Tchan χ N) := by
  intro N
  exact (hPSD_equiv (Tblock N) (directSum (fun χ => Tchan χ N)) (hdiag N)).trans
    (hPSD_directSum (fun χ => Tchan χ N))

end Omega.Zeta
