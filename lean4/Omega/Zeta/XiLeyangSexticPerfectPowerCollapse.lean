import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-leyang-sextic-perfect-power-collapse`. -/
theorem paper_xi_leyang_sextic_perfect_power_collapse (y : ℤ) :
    (128 * y ^ 3 + 219 * y ^ 2 + 69 * y + 16) ^ 2 +
        27 * (-y * (y - 1) * (256 * y ^ 3 + 411 * y ^ 2 + 165 * y + 32)) =
      256 * (2 * y + 1) ^ 6 := by
  ring

end Omega.Zeta
