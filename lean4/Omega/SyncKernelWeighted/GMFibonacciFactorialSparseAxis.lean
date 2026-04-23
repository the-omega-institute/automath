import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Zeta.GmFibonacciSubtowerEntrypointCriterion

namespace Omega.SyncKernelWeighted

open Omega.Zeta

/-- Paper label: `cor:gm-fibonacci-factorial-sparse-axis`. Any positive modulus appears along the
factorial Fibonacci subtower because the Fibonacci entrypoint divides a sufficiently large
factorial, and Fibonacci values respect divisibility of their indices. -/
theorem paper_gm_fibonacci_factorial_sparse_axis (m : ℕ) (hm : 1 ≤ m) :
    ∃ k : ℕ, m ∣ Nat.fib (Nat.factorial (k + 1)) := by
  have hm' : 0 < m := hm
  refine ⟨gmFibonacciEntrypoint m, ?_⟩
  have hentry : m ∣ Nat.fib (gmFibonacciEntrypoint m) := gmFibonacciEntrypoint_dvd_fib hm'
  have hfactorial :
      gmFibonacciEntrypoint m ∣ Nat.factorial (gmFibonacciEntrypoint m + 1) :=
    Nat.dvd_factorial (gmFibonacciEntrypoint_pos hm') (Nat.le_add_right _ _)
  have hfib :
      Nat.fib (gmFibonacciEntrypoint m) ∣ Nat.fib (Nat.factorial (gmFibonacciEntrypoint m + 1)) :=
    Nat.fib_dvd _ _ hfactorial
  exact dvd_trans hentry hfib

end Omega.SyncKernelWeighted
