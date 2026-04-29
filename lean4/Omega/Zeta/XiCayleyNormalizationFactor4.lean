import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `con:xi-four-from-cayley-conformal-factor`. The coefficient `4` in the
Cayley endpoint normalization is the square of the conformal factor `2`, and the associated
denominator identity is purely algebraic. -/
theorem paper_xi_four_from_cayley_conformal_factor (x y : ℝ)
    (hden : x^2 + (1 + y)^2 ≠ 0) :
    (1 - ((x^2 + (1 - y)^2) / (x^2 + (1 + y)^2)) =
        (4 * y) / (x^2 + (1 + y)^2)) ∧
      ((2 : ℝ)^2 / (x^2 + (1 + y)^2) = 4 / (x^2 + (1 + y)^2)) := by
  constructor
  · field_simp [hden]
    ring
  · ring

end Omega.Zeta
