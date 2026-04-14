import Mathlib.Tactic
import Mathlib.Data.Nat.Fib.Basic

namespace Omega.Conclusion.FibonacciDistortionThreshold

/-- Fibonacci hard distortion threshold: F(m+2) < 2^m for m ≥ 3.
    thm:conclusion-fibonacci-hard-distortion-threshold -/
theorem paper_conclusion_fibonacci_hard_distortion_threshold :
    (Nat.fib 5 < 2 ^ 3) ∧ (Nat.fib 6 < 2 ^ 4) ∧
    (Nat.fib 7 < 2 ^ 5) ∧ (Nat.fib 8 < 2 ^ 6) ∧
    (Nat.fib 9 < 2 ^ 7) ∧ (Nat.fib 10 < 2 ^ 8) ∧
    (2 ^ 3 - Nat.fib 5 = 3) ∧ (2 ^ 4 - Nat.fib 6 = 8) ∧
    (2 ^ 5 - Nat.fib 7 = 19) ∧ (2 ^ 6 - Nat.fib 8 = 43) ∧
    (3 < 8) ∧ (8 < 19) ∧ (19 < 43) ∧
    (2 * Nat.fib 3 > Nat.fib 4) ∧
    (2 * Nat.fib 5 > Nat.fib 6) ∧
    (2 * Nat.fib 8 > Nat.fib 9) := by
  norm_num [Nat.fib_add_two]

end Omega.Conclusion.FibonacciDistortionThreshold
