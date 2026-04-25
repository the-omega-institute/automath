import Omega.Zeta.XiTerminalZmKappaSquareCubicFieldS3

namespace Omega.Zeta

/-- Paper label: `prop:xi-terminal-zm-branch-puiseux-coefficient-cubic`. -/
theorem paper_xi_terminal_zm_branch_puiseux_coefficient_cubic :
    (∀ u : ℚ, Omega.Zeta.xiTerminalLambdaFromU u = 3 * (2 * u - 1) / (4 * (3 * u - 2))) ∧
      Omega.Zeta.xiTerminalKappaSquareCubic ((2 : ℚ) / 3) = 4 ∧
      Omega.Zeta.xiTerminalLambdaRationalRootCandidateAudit ∧
      Omega.Zeta.xiTerminalKappaSquareDiscriminant = -((2 : ℤ) ^ 6 * 3 ^ 9 * 37) ∧
      Omega.Zeta.xiTerminalKappaSquareS3Audit := by
  exact paper_xi_terminal_zm_kappa_square_cubic_field_s3

end Omega.Zeta
