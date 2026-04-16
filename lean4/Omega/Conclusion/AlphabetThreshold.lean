import Mathlib.Tactic
import Mathlib.Data.Nat.Fib.Basic

namespace Omega.Conclusion.AlphabetThreshold

/-- Alphabet threshold M ≥ 5 arithmetic seeds.
    cor:conclusion-alphabet-threshold-mge5 -/
theorem paper_conclusion_alphabet_threshold_mge5 :
    (5 : ℕ) ≥ 5 ∧
    (4 * 6 < 27) ∧
    (2 * Nat.fib 10 = 110) ∧ (Nat.fib 11 = 89) ∧
    (4 ^ 4 = 256) ∧
    ((27 : ℕ) > 4 * 4) ∧
    (2 * Nat.fib 5 > Nat.fib 6) ∧
    (2 * Nat.fib 10 > Nat.fib 11) := by
  norm_num [Nat.fib_add_two]

end Omega.Conclusion.AlphabetThreshold
