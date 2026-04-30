import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-terminal-zm-stokes-lambda-critical-rational-in-t`. -/
theorem paper_xi_terminal_zm_stokes_lambda_critical_rational_in_t
    (t y lambda : ℚ)
    (hden : 69 * t + 110 ≠ 0)
    (ht : 162 * t ^ 3 + 1593 * t ^ 2 + 1998 * t + 1184 = 0)
    (hy : y = (36774 * t ^ 2 - 329601 * t - 269488) / (9592 * (69 * t + 110)))
    (hlambda : lambda = -(512 * y ^ 2 + 518 * y + 5) / 279) :
    lambda = -(525411 * t ^ 2 - 4582128 * t - 2625484) /
      (1199 * (69 * t + 110) ^ 2) := by
  rw [hlambda, hy]
  have h_y_den : (9592 * (69 * t + 110) : ℚ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) hden
  have h_goal_den : (1199 * (69 * t + 110) ^ 2 : ℚ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hden)
  have hden_sq : (12100 + t * 15180 + t ^ 2 * 4761 : ℚ) ≠ 0 := by
    have hs : (69 * t + 110) ^ 2 ≠ 0 := pow_ne_zero 2 hden
    contrapose! hs
    nlinarith
  rw [div_eq_div_iff (show (279 : ℚ) ≠ 0 by norm_num) h_goal_den]
  field_simp [h_y_den, hden, h_goal_den, hden_sq]
  ring_nf at ht ⊢
  field_simp [hden_sq]
  ring_nf
  apply sub_eq_zero.mp
  ring_nf
  rw [show
      701160870974562662400 + t * 1989430776886333461120 +
            t ^ 2 * 2487650953071403335744 + t ^ 3 * 1461903754818515149152 +
          t ^ 4 * 308831531659409989296 +
        (-(t ^ 5 * 13720104093652498080) - t ^ 6 * 3952474430153914368) =
        (-39192912 * (69 * t + 110) ^ 2 * (130752 * t - 1248743)) *
          (1184 + t * 1998 + t ^ 2 * 1593 + t ^ 3 * 162) by
      ring]
  rw [ht]
  ring

end Omega.Zeta
