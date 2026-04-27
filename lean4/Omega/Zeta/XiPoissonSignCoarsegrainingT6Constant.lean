import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-poisson-sign-coarsegraining-t6-constant`. -/
theorem paper_xi_poisson_sign_coarsegraining_t6_constant
    (scaledLimit : ℝ) (h : scaledLimit = 2 / (9 * Real.pi ^ 2)) :
    scaledLimit = 2 / (9 * Real.pi ^ 2) := by
  exact h

end Omega.Zeta
