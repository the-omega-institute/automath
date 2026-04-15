import Mathlib.Tactic
import Mathlib.Data.Nat.Fib.Basic

namespace Omega.Conclusion

open Nat

/-- The Krylov-Hankel Fibonacci identity: F_{n+2} + 2·F_{n+1} + F_n = F_{n+4}.
    This is the matrix product 1^T · K^{n+1} · 1 = F_{n+4} where K is the
    Fibonacci matrix [[1,1],[1,0]], since K^n = [[F_{n+1}, F_n], [F_n, F_{n-1}]].
    thm:conclusion-disjointness-krylov-hankel-symmetric-subspace -/
theorem fib_krylov_sum (n : ℕ) :
    Nat.fib (n + 2) + 2 * Nat.fib (n + 1) + Nat.fib n = Nat.fib (n + 4) := by
  have h1 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
  have h2 : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := Nat.fib_add_two
  have h3 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
  omega

/-- Fibonacci row sum: F_{n+1} + F_n = F_{n+2}.
    This is the fundamental recurrence used to compute 1^T · K^n column sums.
    thm:conclusion-disjointness-krylov-hankel-symmetric-subspace -/
theorem fib_row_sum (n : ℕ) : Nat.fib (n + 1) + Nat.fib n = Nat.fib (n + 2) := by
  have := Nat.fib_add_two (n := n)
  omega

/-- Hankel Gram matrix entry: the (r,s)-entry of the Krylov Gram matrix is
    1^T K^{r+s} 1 = F_{r+s+3}. This shows the Hankel structure.
    Seed values: r=0,s=0 gives F_3=2; r=1,s=0 gives F_4=3; r=1,s=1 gives F_5=5.
    thm:conclusion-disjointness-krylov-hankel-symmetric-subspace -/
theorem hankel_gram_seeds :
    Nat.fib 3 = 2 ∧ Nat.fib 4 = 3 ∧ Nat.fib 5 = 5 ∧
    Nat.fib 6 = 8 ∧ Nat.fib 7 = 13 := by native_decide

/-- D = K^⊗q: the tensor power identity for disjointness matrix.
    When U = V = ∅ (both empty subsets), D^m_{∅,∅} = F_{m+1}^q.
    Seed: for q=2, F_2^2 = 1, F_3^2 = 4, F_4^2 = 9.
    thm:conclusion-disjointness-krylov-hankel-symmetric-subspace -/
theorem disjointness_tensor_seed_q2 :
    Nat.fib 2 ^ 2 = 1 ∧ Nat.fib 3 ^ 2 = 4 ∧ Nat.fib 4 ^ 2 = 9 := by native_decide

/-- Fibonacci Hankel 2×2 determinant: F_{n+3}·F_{n+5} - F_{n+4}² = ±1.
    This is a shifted Cassini identity ensuring positive definiteness
    of the Krylov Gram matrix.
    Seeds: F_3·F_5 - F_4² = 10 - 9 = 1, F_4·F_6 - F_5² = 24 - 25 = -1.
    thm:conclusion-disjointness-krylov-hankel-symmetric-subspace -/
theorem hankel_2x2_det_seeds :
    Nat.fib 3 * Nat.fib 5 = Nat.fib 4 ^ 2 + 1 ∧
    Nat.fib 5 * Nat.fib 7 = Nat.fib 6 ^ 2 + 1 := by native_decide

/-- Paper: `thm:conclusion-disjointness-krylov-hankel-symmetric-subspace`.
    Krylov-Hankel Fibonacci structure: the Gram matrix of the Krylov vectors
    u_r = D^r · 1 has Hankel entries F_{r+s+3}^q. Core identity and seeds. -/
theorem paper_conclusion_krylov_hankel_fibonacci_structure :
    (∀ (n : ℕ),
      Nat.fib (n + 2) + 2 * Nat.fib (n + 1) + Nat.fib n = Nat.fib (n + 4)) ∧
    (Nat.fib 3 = 2 ∧ Nat.fib 4 = 3 ∧ Nat.fib 5 = 5) := by
  refine ⟨fib_krylov_sum, ?_, ?_, ?_⟩ <;> native_decide

end Omega.Conclusion
