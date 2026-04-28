import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete certificate for the boundary `Z/2^3` action: three independent odd-character
coordinates are visibly separated inside a linear coordinate set of size `visibleDimension`. -/
structure xi_window6_boundary_minimal_linear_visible_dimension_data where
  visibleDimension : ℕ
  oddPrime : ℕ
  oddPrime_isPrime : Nat.Prime oddPrime
  oddPrime_ne_two : oddPrime ≠ 2
  characterCoordinate : Fin 3 → Fin visibleDimension
  characterCoordinate_injective : Function.Injective characterCoordinate

namespace xi_window6_boundary_minimal_linear_visible_dimension_data

/-- The visible linear coordinate space has dimension at least three. -/
def statement (D : xi_window6_boundary_minimal_linear_visible_dimension_data) : Prop :=
  3 ≤ D.visibleDimension

end xi_window6_boundary_minimal_linear_visible_dimension_data

/-- Paper label: `thm:xi-window6-boundary-minimal-linear-visible-dimension`. -/
theorem paper_xi_window6_boundary_minimal_linear_visible_dimension
    (D : xi_window6_boundary_minimal_linear_visible_dimension_data) : D.statement := by
  have hcard := Fintype.card_le_of_injective D.characterCoordinate D.characterCoordinate_injective
  simpa [xi_window6_boundary_minimal_linear_visible_dimension_data.statement] using hcard

end Omega.Zeta
