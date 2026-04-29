import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-terminal-zm-leyang-branchdata-quadratic-reconstruction`. -/
theorem paper_xi_terminal_zm_leyang_branchdata_quadratic_reconstruction
    (u lambda0 y0 beta : ℚ)
    (hLambda : 16 * lambda0 + 31 = 108 * u * (1 - u))
    (hy : 256 * y0 + 1091 = 108 * u * (25 - 21 * u))
    (hBeta : 72 * beta + 22 = 9 * u * (10 * u - 1)) :
    lambda0 = -31 / 16 + 27 / 4 * u - 27 / 4 * u ^ 2 ∧
      y0 = -1091 / 256 + 675 / 64 * u - 567 / 64 * u ^ 2 ∧
      beta = -11 / 36 - 1 / 8 * u + 5 / 4 * u ^ 2 := by
  constructor
  · nlinarith [hLambda]
  constructor
  · nlinarith [hy]
  · nlinarith [hBeta]

end Omega.Zeta
