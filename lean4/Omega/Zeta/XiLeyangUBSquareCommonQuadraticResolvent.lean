import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-leyang-u-b-square-common-quadratic-resolvent`. -/
theorem paper_xi_leyang_u_b_square_common_quadratic_resolvent :
    ((-((2 : ℚ) ^ 2 * 3 ^ 9 * 11 ^ 2 * 37 * 109 ^ 2)) /
          (-((2 : ℚ) ^ 6 * 3 ^ 9 * 37)) = ((1199 : ℚ) / 4) ^ 2) ∧
      (-((2 : ℤ) ^ 6 * 3 ^ 9 * 37) = -(((2 : ℤ) ^ 3 * 3 ^ 4) ^ 2) * 111) := by
  norm_num

end Omega.Zeta
