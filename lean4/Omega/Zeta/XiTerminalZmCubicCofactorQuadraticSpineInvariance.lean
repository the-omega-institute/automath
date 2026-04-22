import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmCubicCofactorDiscriminantKernelS3RigidityHeight

namespace Omega.Zeta

/-- Paper label: `cor:xi-terminal-zm-cubic-cofactor-quadratic-spine-invariance`. The previously
proved square-elimination identity already shows that the cubic-cofactor discriminant differs from
`-B(y)` by the explicit rational square `(2xw + 3x² - 1)²`. -/
theorem paper_xi_terminal_zm_cubic_cofactor_quadratic_spine_invariance (x y w : ℚ)
    (hy : y = x ^ 2 + (w - 1) / 2) (hw : w ^ 2 = 4 * x ^ 3 - 4 * x + 1)
    (hderiv : 2 * x * w + 3 * x ^ 2 - 1 ≠ 0) :
    ∃ u : ℚ, xiTerminalCubicCofactorDiscriminant x y * u ^ 2 = -xiTerminalB y := by
  refine ⟨2 * x * w + 3 * x ^ 2 - 1, ?_⟩
  simpa using
    (paper_xi_terminal_zm_cubic_cofactor_disc_derivative_square_elimination x y w hy hw
      hderiv).2.2.2.2

end Omega.Zeta
