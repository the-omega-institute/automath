import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-terminal-zm-stokes-b2-quadratic-resolvent`. -/
theorem paper_xi_terminal_zm_stokes_b2_quadratic_resolvent :
    ∃ u : ℤ, -((2 : ℤ) ^ 2 * 3 ^ 9 * 11 ^ 2 * 37 * 109 ^ 2) = -111 * u ^ 2 := by
  refine ⟨2 * 3 ^ 4 * 11 * 109, ?_⟩
  norm_num

end Omega.Zeta
