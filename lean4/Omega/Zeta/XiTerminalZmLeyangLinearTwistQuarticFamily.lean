import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-terminal-zm-leyang-linear-twist-quartic-family`. -/
theorem paper_xi_terminal_zm_leyang_linear_twist_quartic_family (t X Y : ℚ) :
    let y : ℚ := X^2 + t * X + Y - (1 / 2 : ℚ)
    Y^2 = X^3 - X + (1 / 4 : ℚ) →
      X^4 + (2 * t - 1) * X^3 + (t^2 - 2 * y - 1) * X^2 +
        (1 - t - 2 * t * y) * X + y * (y + 1) = 0 := by
  dsimp
  intro hY
  have hquartic :
      X^4 + (2 * t - 1) * X^3 +
          (t^2 - 2 * (X^2 + t * X + Y - (1 / 2 : ℚ)) - 1) * X^2 +
          (1 - t - 2 * t * (X^2 + t * X + Y - (1 / 2 : ℚ))) * X +
          (X^2 + t * X + Y - (1 / 2 : ℚ)) * ((X^2 + t * X + Y - (1 / 2 : ℚ)) + 1) =
        Y^2 - (X^3 - X + (1 / 4 : ℚ)) := by
    ring
  linarith

end Omega.Zeta
