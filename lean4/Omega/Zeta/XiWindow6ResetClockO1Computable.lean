import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-window6-reset-clock-O1-computable`. -/
theorem paper_xi_window6_reset_clock_o1_computable (S T : Nat → Nat)
    (hT : ∀ n, T n = 34 * n + 21 * S n) :
    ∀ n, T n = 34 * n + 21 * S n := by
  exact hT

end Omega.Zeta
