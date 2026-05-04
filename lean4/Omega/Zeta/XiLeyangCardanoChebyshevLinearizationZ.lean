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

/-- Paper label: `cor:xi-leyang-chebyshev-normal-form-and-discriminant-recovery`. -/
theorem paper_xi_leyang_chebyshev_normal_form_and_discriminant_recovery
    (A u y t : Rat) (hy : 2 * y + 1 != 0)
    (ht : t = A / (8 * (2 * y + 1) ^ 3))
    (hcurve : 256 * (2 * y + 1) ^ 6 - A ^ 2 = 27 * u ^ 2) :
    (-4 * (-3 : Rat) ^ 3 - 27 * (-t) ^ 2 = 27 * (4 - t ^ 2)) ∧
      27 * (4 - t ^ 2) =
        (3 ^ 6 / 2 ^ 6) * (u ^ 2 / (2 * y + 1) ^ 6) := by
  constructor
  · ring
  · subst t
    have hy_ne : 2 * y + 1 ≠ 0 := by
      simpa using hy
    field_simp [hy_ne]
    ring_nf at hcurve ⊢
    linarith

end Omega.Zeta
