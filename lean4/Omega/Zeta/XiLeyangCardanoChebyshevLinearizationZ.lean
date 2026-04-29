import Mathlib.Tactic

namespace Omega.Zeta

/-- Cardano--Chebyshev trace linearization for the cubic Kummer coordinate and the associated
`z`-coordinate expression.
    thm:xi-leyang-cardano-chebyshev-linearization-z -/
theorem paper_xi_leyang_cardano_chebyshev_linearization_z {K : Type*} [Field K]
    (xi eta s z y : K) (hxi : xi ≠ 0) (heta : eta = xi ^ 3)
    (hs : s = xi + xi⁻¹) (hz : z = ((2 * y + 1) / 3) * (2 * s - 1)) :
    eta + eta⁻¹ = s ^ 3 - 3 * s ∧
      z = ((2 * y + 1) / 3) * (2 * (xi + xi⁻¹) - 1) := by
  constructor
  · subst eta
    subst s
    field_simp [hxi]
    ring
  · simpa [hs] using hz

end Omega.Zeta
