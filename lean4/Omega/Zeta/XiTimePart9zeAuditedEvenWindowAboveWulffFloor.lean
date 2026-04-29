import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-time-part9ze-audited-even-window-above-wulff-floor`. -/
theorem paper_xi_time_part9ze_audited_even_window_above_wulff_floor :
    ((21 * 3 ^ 2 + 11 * 5 ^ 2 + 23 * 6 ^ 2 : ℚ) / 256 ^ 2 -
          (19 * 4 ^ 2 + 36 * 5 ^ 2 : ℚ) / 256 ^ 2 =
        11 / 8192) ∧
      ((55 * 5 ^ 2 + 52 * 8 ^ 2 + 37 * 9 ^ 2 : ℚ) / 1024 ^ 2 -
            (128 * 7 ^ 2 + 16 * 8 ^ 2 : ℚ) / 1024 ^ 2 =
          101 / 262144) ∧
        ((144 * 8 ^ 2 + 85 * 12 ^ 2 + 148 * 13 ^ 2 : ℚ) / 4096 ^ 2 -
              (51 * 10 ^ 2 + 326 * 11 ^ 2 : ℚ) / 4096 ^ 2 =
            961 / 8388608) := by
  norm_num

end Omega.Zeta
