import Mathlib.Data.Finset.Card

namespace Omega.Zeta

/-- Paper label: `cor:xi-zero-dispersion-kink-count-under-composition`. -/
theorem paper_xi_zero_dispersion_kink_count_under_composition
    (K₁ K₂ Kcomp : Finset ℕ) (hsub : Kcomp ⊆ K₁ ∪ K₂) :
    Kcomp.card ≤ K₁.card + K₂.card := by
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le K₁ K₂)

end Omega.Zeta
