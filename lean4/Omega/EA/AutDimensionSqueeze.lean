import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

/-!
# Aut dimension golden squeeze seed values

Fibonacci values and power-of-4 quotients for the automorphism dimension
golden-ratio squeeze theorem.
-/

namespace Omega.EA

/-- Aut dimension golden squeeze seeds.
    thm:fold-aut-dimension-golden-squeeze -/
theorem paper_ea_aut_dimension_golden_squeeze_seeds :
    (Nat.fib 4 = 3 ∧ 4 ^ 2 = 16 ∧ 16 / 3 = 5) ∧
    (Nat.fib 5 = 5 ∧ 4 ^ 3 = 64 ∧ 64 / 5 = 12) ∧
    (Nat.fib 6 = 8 ∧ 4 ^ 4 = 256 ∧ 256 / 8 = 32) ∧
    (6 - 3 = 3 ∧ 18 - 5 = 13) ∧
    (4 * 5 = 20 ∧ 2 * 2 = 4) := by
  refine ⟨⟨by decide, by norm_num, by norm_num⟩,
         ⟨by decide, by norm_num, by norm_num⟩,
         ⟨by decide, by norm_num, by norm_num⟩,
         ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

end Omega.EA
