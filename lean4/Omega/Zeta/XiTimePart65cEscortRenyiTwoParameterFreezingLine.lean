import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part65c-escort-renyi-two-parameter-freezing-line`. -/
theorem paper_xi_time_part65c_escort_renyi_two_parameter_freezing_line
    (P : ℕ → ℝ) (a s : ℕ) (alpha g : ℝ) (hs : 2 ≤ s)
    (hPa : P a = (a : ℝ) * alpha + g)
    (hPas : P (a * s) = ((a * s : ℕ) : ℝ) * alpha + g) :
    ((s : ℝ) * P a - P (a * s)) / ((s : ℝ) - 1) = g := by
  have hs_ne_one : (s : ℝ) ≠ 1 := by
    norm_num [ne_eq, show s ≠ 1 by omega]
  have hden : (s : ℝ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr hs_ne_one
  rw [hPa, hPas]
  field_simp [hden]
  norm_num
  ring

end Omega.Zeta
