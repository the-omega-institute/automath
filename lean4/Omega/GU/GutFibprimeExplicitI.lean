import Omega.GU.FibPrimePisano

namespace Omega.GU

/-- Paper-facing wrapper for the explicit Fibonacci-prime square roots of `-1`.
    cor:gut-fibprime-explicit-i -/
theorem paper_gut_fibprime_explicit_i :
    (Nat.fib 4) ^ 2 % (Nat.fib 5) = Nat.fib 5 - 1 ∧
    (Nat.fib 8) ^ 2 % (Nat.fib 7) = Nat.fib 7 - 1 ∧
    (Nat.fib 12) ^ 2 % (Nat.fib 11) = Nat.fib 11 - 1 ∧
    (Nat.fib 14) ^ 2 % (Nat.fib 13) = Nat.fib 13 - 1 := by
  exact paper_fibprime_explicit_sqrt_neg_one

end Omega.GU
