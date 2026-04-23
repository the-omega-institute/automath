import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-window6-reset-clock-bounded-drift`. Writing the reset clock as
`T_n = 34 n + 21 S_n`, the drift from the mean slope `34 + 21 / φ` is exactly
`21 * (S_n - n / φ)`, so the Beatty/Sturmian balance bound gives a uniform error at most `21`. -/
theorem paper_xi_window6_reset_clock_bounded_drift (n S : ℕ) (φ : ℝ)
    (hbal : |(S : ℝ) - (n : ℝ) / φ| ≤ 1) :
    |((34 * n + 21 * S : ℕ) : ℝ) - (n : ℝ) * (34 + 21 / φ)| ≤ 21 := by
  have hrewrite :
      (((34 * n + 21 * S : ℕ) : ℝ) - (n : ℝ) * (34 + 21 / φ)) =
        21 * ((S : ℝ) - (n : ℝ) / φ) := by
    norm_num
    ring
  have habs :
      |((34 * n + 21 * S : ℕ) : ℝ) - (n : ℝ) * (34 + 21 / φ)| =
        21 * |(S : ℝ) - (n : ℝ) / φ| := by
    rw [hrewrite, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 21)]
  have hmul : 21 * |(S : ℝ) - (n : ℝ) / φ| ≤ 21 := by
    nlinarith
  rw [habs]
  exact hmul

end Omega.Zeta
