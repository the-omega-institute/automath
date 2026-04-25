import Mathlib.Tactic

namespace Omega.GU

/-- prop:bdry-gap-33-cassini-factorization -/
theorem paper_bdry_gap_33_cassini_factorization :
    Nat.fib 9 - Nat.fib 2 = Nat.fib 4 * (Nat.fib 6 + Nat.fib 4) ∧
      Nat.fib 9 - Nat.fib 2 = 33 := by
  norm_num [Nat.fib]

end Omega.GU
