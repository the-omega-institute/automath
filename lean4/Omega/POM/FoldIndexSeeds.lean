import Mathlib.Tactic
import Mathlib.Data.Nat.Fib.Basic

namespace Omega.POM.FoldIndexSeeds

/-- Fold index I_m = 2^m / F(m+2) seeds.
    cor:pom-Kk-sine-product-sum -/
theorem paper_pom_fold_index_seeds :
    (2 ^ 3 / Nat.fib 5 = 1) ∧
    (2 ^ 4 / Nat.fib 6 = 2) ∧
    (2 ^ 5 / Nat.fib 7 = 2) ∧
    (2 ^ 6 / Nat.fib 8 = 3) ∧
    (2 ^ 7 / Nat.fib 9 = 3) ∧
    (1 * Nat.fib 5 < 2 ^ 3) ∧ (2 * Nat.fib 5 > 2 ^ 3) ∧
    (2 * Nat.fib 6 = 2 ^ 4) ∧
    (2 * Nat.fib 7 < 2 ^ 5) ∧ (3 * Nat.fib 7 > 2 ^ 5) ∧
    (2 ^ 4 = 2 * Nat.fib 6) ∧
    (Nat.fib 5 = 5) ∧ (Nat.fib 6 = 8) ∧
    (Nat.fib 7 = 13) ∧ (Nat.fib 8 = 21) ∧ (Nat.fib 9 = 34) := by
  norm_num [Nat.fib_add_two]

end Omega.POM.FoldIndexSeeds
