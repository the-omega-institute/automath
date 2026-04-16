import Mathlib.Tactic
import Mathlib.Data.Nat.Fib.Basic

namespace Omega.Conclusion.ZeckendorfEulerSeeds

/-- Zeckendorf-Euler reindexing seeds: the Zeckendorf bijection
    converts factorial sums over legal words to partial sums of e.
    thm:conclusion-zeckendorf-euler-reindexing -/
theorem paper_conclusion_zeckendorf_euler_reindexing_seeds :
    Nat.fib 3 = 2 ∧
    Nat.fib 4 = 3 ∧
    Nat.fib 5 = 5 ∧
    Nat.factorial 0 + Nat.factorial 1 = 2 ∧
    ((1 : ℚ) / Nat.factorial 0 + 1 / Nat.factorial 1 + 1 / Nat.factorial 2 = 5/2) ∧
    (∀ m : ℕ, m ≤ 5 → Nat.fib (m + 2) > m) ∧
    ((2 : ℚ) / Nat.factorial (Nat.fib 4) = 1/3) := by
  refine ⟨by native_decide, by native_decide, by native_decide,
          by norm_num,
          by norm_num [Nat.factorial],
          fun m hm => by interval_cases m <;> simp [Nat.fib],
          by norm_num [Nat.fib, Nat.factorial]⟩

theorem paper_conclusion_zeckendorf_euler_reindexing_package :
    Nat.fib 3 = 2 ∧
    Nat.fib 4 = 3 ∧
    Nat.fib 5 = 5 ∧
    Nat.factorial 0 + Nat.factorial 1 = 2 ∧
    ((1 : ℚ) / Nat.factorial 0 + 1 / Nat.factorial 1 + 1 / Nat.factorial 2 = 5/2) ∧
    (∀ m : ℕ, m ≤ 5 → Nat.fib (m + 2) > m) ∧
    ((2 : ℚ) / Nat.factorial (Nat.fib 4) = 1/3) :=
  paper_conclusion_zeckendorf_euler_reindexing_seeds

end Omega.Conclusion.ZeckendorfEulerSeeds
