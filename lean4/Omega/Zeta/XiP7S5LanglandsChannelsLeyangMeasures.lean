import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-p7-s5-langlands-channels-leyang-measures`. -/
theorem paper_xi_p7_s5_langlands_channels_leyang_measures :
    ((77 : ℚ) / 240 + 3 / 16 + 2 * (1 / 16) + 2 * (1 / 12) + 4 * (1 / 20) = 1) ∧
      ((29 : ℚ) / 100 + 11 / 60 + 2 * (1 / 20) + 2 * (1 / 10) + 2 * (1 / 30) +
          4 * (1 / 25) = 1) ∧
        ((17 : ℚ) / 60 + 7 / 36 + 2 * (1 / 12) + 2 * (1 / 12) + 2 * (1 / 36) +
            4 * (1 / 30) = 1) := by
  norm_num

end Omega.Zeta
