import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-time-part9x-window6-boundary-arithmetic-pinning`. -/
theorem paper_xi_time_part9x_window6_boundary_arithmetic_pinning :
    (1 + Nat.fib 7 = 14) ∧
      (1 + Nat.fib 4 + Nat.fib 7 = 17) ∧
      (1 + Nat.fib 5 + Nat.fib 7 = 19) ∧
      (17 - 14 = 3) ∧
      (19 - 17 = 2) ∧
      (19 - 14 = 5) ∧
      ¬ (7 ∣ 3) ∧
      Nat.gcd 14 21 = 7 := by
  norm_num [Nat.fib]

end Omega.Zeta
