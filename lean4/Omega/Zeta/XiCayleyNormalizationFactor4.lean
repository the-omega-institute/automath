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

/-- Paper label: `con:xi-four-rescales-under-cayley-gauge`. Under a Cayley gauge with scale
`lambda`, the squared endpoint conformal factor rescales the coefficient `4` to
`4 * lambda^2`, and the normalization returns to the fixed gauge when `lambda = 1`. -/
theorem paper_con_xi_four_rescales_under_cayley_gauge (lambda x y : ℝ)
    (hden : x^2 + (lambda + y)^2 ≠ 0) :
    ((2 * lambda)^2 / (x^2 + (lambda + y)^2) =
        (4 * lambda^2) / (x^2 + (lambda + y)^2)) ∧
      (lambda = 1 →
        (4 * lambda^2) / (x^2 + (lambda + y)^2) = 4 / (x^2 + (1 + y)^2)) := by
  constructor
  · ring
  · intro hlambda
    subst lambda
    ring

end Omega.Zeta
