import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part74-finite-past-primeslice-complexity-depth`. -/
theorem paper_xi_time_part74_finite_past_primeslice_complexity_depth
    (N cN : Nat) (h_lower : N ≤ cN) (h_upper : cN ≤ N) : cN = N := by
  exact le_antisymm h_upper h_lower

end Omega.Zeta
