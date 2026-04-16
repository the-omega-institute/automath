import Mathlib.Tactic
import Omega.Core.Fib

namespace Omega.Folding.EndpointUnique

open Nat Finset

/-- Alternating Fibonacci sum (odd terms): ∑_{i<k} F_{2i+3} = F_{2k+2} - 1.
    prop:fold-endpoint-Mm-minus-one-unique -/
theorem alternating_fib_sum_even (k : ℕ) :
    ∑ i ∈ Finset.range k, Nat.fib (2 * i + 3) = Nat.fib (2 * k + 2) - 1 := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : 1 ≤ Nat.fib (2 * n + 2) := Nat.fib_pos.mpr (by omega)
    have hrec : Nat.fib (2 * (n + 1) + 2) = Nat.fib (2 * n + 2) + Nat.fib (2 * n + 3) := by
      rw [show 2 * (n + 1) + 2 = (2 * n + 2) + 2 from by omega]
      exact Nat.fib_add_two
    omega

/-- Alternating Fibonacci sum (even terms): ∑_{i<k} F_{2i+2} = F_{2k+1} - 1.
    prop:fold-endpoint-Mm-minus-one-unique -/
theorem alternating_fib_sum_odd (k : ℕ) :
    ∑ i ∈ Finset.range k, Nat.fib (2 * i + 2) = Nat.fib (2 * k + 1) - 1 := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : 1 ≤ Nat.fib (2 * n + 1) := Nat.fib_pos.mpr (by omega)
    have hrec : Nat.fib (2 * (n + 1) + 1) = Nat.fib (2 * n + 1) + Nat.fib (2 * n + 2) := by
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 from by omega]
      exact Nat.fib_add_two
    omega

/-- Paper seeds: endpoint Fibonacci sums at small indices.
    prop:fold-endpoint-Mm-minus-one-unique -/
theorem paper_fold_endpoint_seeds :
    Nat.fib 3 = Nat.fib 4 - 1 ∧
    Nat.fib 4 + Nat.fib 2 = Nat.fib 5 - 1 ∧
    Nat.fib 5 + Nat.fib 3 = Nat.fib 6 - 1 ∧
    Nat.fib 6 + Nat.fib 4 + Nat.fib 2 = Nat.fib 7 - 1 := by
  native_decide

end Omega.Folding.EndpointUnique
