import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-leakage-additivity-directsum`. Direct-sum determinant
factorization transfers pointwise to the zeta-channel factorization. -/
theorem paper_xi_leakage_additivity_directsum {α β : Type*} [CommMonoid β]
    (Delta Delta1 Delta2 Xi Xi1 Xi2 : α → β)
    (hDelta : ∀ x, Delta x = Delta1 x * Delta2 x)
    (hXi : ∀ x, Xi x = Delta x)
    (hXi1 : ∀ x, Xi1 x = Delta1 x)
    (hXi2 : ∀ x, Xi2 x = Delta2 x) :
    ∀ x, Xi x = Xi1 x * Xi2 x := by
  intro x
  rw [hXi x, hDelta x, hXi1 x, hXi2 x]

end Omega.Zeta
