import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-terminal-zm-stokes-t-elliptic-branch-coordinate`. -/
theorem paper_xi_terminal_zm_stokes_t_elliptic_branch_coordinate
    (alpha y t : ℚ)
    (h_alpha : 16 * alpha ^ 3 - 9 * alpha ^ 2 + 1 = 0)
    (h_alpha_ne : alpha ≠ 0)
    (h_y : 4 * alpha * y = 4 * alpha ^ 3 - 3 * alpha ^ 2 - 2 * alpha + 1)
    (h_den1 : alpha ^ 2 * (12 * alpha ^ 2 - 6 * alpha - 4 * y - 2) ≠ 0)
    (h_den2 : 3 * (1831 * alpha ^ 2 + 144 * alpha - 175) ≠ 0)
    (h_t :
      t =
        (-2 * y * (-2 * alpha ^ 2 + 2 * y + 1)) /
          (alpha ^ 2 * (12 * alpha ^ 2 - 6 * alpha - 4 * y - 2))) :
    t = (2 * (1113 * alpha ^ 2 - 2192 * alpha + 303)) /
      (3 * (1831 * alpha ^ 2 + 144 * alpha - 175)) := by
  have h_branch_linear : 6 * alpha ^ 2 - 3 * alpha + 2 * y + 1 = 0 := by
    have hmul : alpha * (6 * alpha ^ 2 - 3 * alpha + 2 * y + 1) = 0 := by
      ring_nf at h_alpha h_y ⊢
      nlinarith [h_alpha, h_y]
    exact (mul_eq_zero.mp hmul).resolve_left h_alpha_ne
  have hy : y = (-6 * alpha ^ 2 + 3 * alpha - 1) / 2 := by
    nlinarith [h_branch_linear]
  rw [h_t]
  rw [div_eq_div_iff h_den1 h_den2]
  rw [hy]
  ring_nf at h_alpha h_y ⊢
  linear_combination (-19818 * alpha ^ 3 + 10221 * alpha ^ 2 - 1575 * alpha) * h_alpha

end Omega.Zeta
