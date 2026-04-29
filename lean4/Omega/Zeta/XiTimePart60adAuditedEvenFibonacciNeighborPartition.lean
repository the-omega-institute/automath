import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part60ad-audited-even-fibonacci-neighbor-partition`. -/
theorem paper_xi_time_part60ad_audited_even_fibonacci_neighbor_partition :
    (8 + 13 = Nat.fib 8 ∧ 8 = Nat.fib 6 ∧ 13 = Nat.fib 7) ∧
      (21 + 34 = Nat.fib 10 ∧ 21 = Nat.fib 8 ∧ 34 = Nat.fib 9) ∧
        (55 + 89 = Nat.fib 12 ∧ 55 = Nat.fib 10 ∧ 89 = Nat.fib 11) ∧
          (144 + 233 = Nat.fib 14 ∧ 144 = Nat.fib 12 ∧ 233 = Nat.fib 13) := by
  norm_num [Nat.fib]

end Omega.Zeta
