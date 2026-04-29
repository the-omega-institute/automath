import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label:
`cor:xi-time-part9zg-leyang-quadratic-character-perfect-single-root-detector`. -/
theorem paper_xi_time_part9zg_leyang_quadratic_character_perfect_single_root_detector :
    (2 : ℚ) * (3 / 6) = 1 ∧
      (2 : ℚ) * (1 / 6) = 1 / 3 ∧
        (2 : ℚ) * (2 / 6) = 2 / 3 := by
  norm_num

end Omega.Zeta
