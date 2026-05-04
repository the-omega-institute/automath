import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-ed-discriminant-j-closed-form`. -/
theorem paper_xi_ed_discriminant_j_closed_form :
    (((112 : ℚ) / 3) ^ 3 - 27 * ((667 : ℚ) / 27) ^ 2 = (31 : ℚ) ^ 2 * 37) ∧
      ((31 : ℚ) ^ 2 * 37 = 35557) ∧
      (1728 * (((112 : ℚ) / 3) ^ 3) / ((31 : ℚ) ^ 2 * 37) =
        ((2 : ℚ) ^ 18 * 7 ^ 3) / ((31 : ℚ) ^ 2 * 37)) ∧
      (((2 : ℚ) ^ 18 * 7 ^ 3) / ((31 : ℚ) ^ 2 * 37) = 89915392 / 35557) := by
  norm_num

end Omega.Zeta
