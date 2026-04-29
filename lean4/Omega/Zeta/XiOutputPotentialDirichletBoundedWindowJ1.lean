import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-output-potential-dirichlet-bounded-window-j1`. -/
theorem paper_xi_output_potential_dirichlet_bounded_window_j1 (theta : Nat → Nat → ℝ)
    (hdom :
      ∀ J : Nat, 2 ≤ J → ∃ m0 : Nat, ∀ m j : Nat, m0 ≤ m → 2 ≤ j → j ≤ J →
        theta m 1 > theta m j) :
    ∀ J : Nat, 2 ≤ J → ∃ m0 : Nat, ∀ m j : Nat, m0 ≤ m → 2 ≤ j → j ≤ J →
      theta m 1 > theta m j := by
  exact hdom

end Omega.Zeta
