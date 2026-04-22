import Mathlib.Tactic

namespace Omega.Zeta

/-- Exact arithmetic for the optimal two-orbit `W(B₃)`-invariant compression of the window-6
fiber multiplicity field.
    thm:xi-window6-weyl-invariant-best-two-orbit-compression -/
theorem paper_xi_window6_weyl_invariant_best_two_orbit_compression :
    ((5 : ℚ) * 4 + 2) / 6 = 11 / 3 ∧
      ((4 : ℚ) * 4 + 4 * 3 + 4 * 2) / 12 = 3 ∧
      (((5 : ℚ) * (4 - 11 / 3)^2 + (2 - 11 / 3)^2 + 4 * (4 - 3)^2 + 4 * (3 - 3)^2 +
          4 * (2 - 3)^2) / 18 = 17 / 27) ∧
      max (max |(2 : ℚ) - 3| |(4 : ℚ) - 3|) (max |(2 : ℚ) - 3| (max |(3 : ℚ) - 3| |(4 : ℚ) - 3|)) = 1 := by
  norm_num

end Omega.Zeta
