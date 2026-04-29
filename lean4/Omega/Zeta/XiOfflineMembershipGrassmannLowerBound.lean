import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete cardinal form of the offline Grassmann-membership lower bound.
If a zero-error offline certificate gives an injective encoding of the Grassmann data into
`ell` bits, and the Grassmann family has the advertised Gaussian-binomial lower bound, then the
same lower bound is forced on the bitstring space. -/
def xi_offline_membership_grassmann_lower_bound_claim : Prop :=
  ∀ p n r ell grassmannCard : ℕ,
    r ≤ n →
      p ^ (r * (n - r)) ≤ grassmannCard →
        (∃ encode : Fin grassmannCard → Fin (2 ^ ell), Function.Injective encode) →
          p ^ (r * (n - r)) ≤ 2 ^ ell

/-- Paper label: `thm:xi-offline-membership-grassmann-lower-bound`. -/
theorem paper_xi_offline_membership_grassmann_lower_bound :
    xi_offline_membership_grassmann_lower_bound_claim := by
  intro p n r ell grassmannCard _hr hGrassmann hencode
  rcases hencode with ⟨encode, hInjective⟩
  have hCounting : grassmannCard ≤ 2 ^ ell := by
    have hcard := Fintype.card_le_of_injective encode hInjective
    simpa using hcard
  exact le_trans hGrassmann hCounting

end Omega.Zeta
