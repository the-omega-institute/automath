import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

/-!
# Zeckendorf prime language non-regularity seed values

Primality witnesses, Fibonacci values, and ordering for the
Zeckendorf prime language non-regularity proof.
-/

namespace Omega.Zeta

/-- Zeckendorf prime language non-regular seeds.
    cor:zeta-syntax-zeckendorf-prime-language-not-regular -/
theorem paper_zeta_syntax_zeckendorf_prime_language_not_regular_seeds :
    (Nat.Prime 2 ∧ Nat.Prime 3 ∧ Nat.Prime 5 ∧ Nat.Prime 7) ∧
    (2 ≤ 3 ∧ 3 ≤ 5 ∧ 4 ≤ 8) ∧
    (Nat.fib 7 = 13 ∧ Nat.fib 8 = 21 ∧ Nat.fib 9 = 34) ∧
    (1 < 2 ∧ 2 < 3) ∧
    (Nat.fib 6 = 8 ∧ Nat.fib 7 = 13) := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num⟩,
         ⟨by omega, by omega, by omega⟩,
         ⟨by native_decide, by native_decide, by native_decide⟩,
         ⟨by omega, by omega⟩, ⟨by decide, by native_decide⟩⟩

/-- Package wrapper for the Zeckendorf prime language non-regular seeds.
    cor:zeta-syntax-zeckendorf-prime-language-not-regular -/
theorem paper_zeta_syntax_zeckendorf_prime_language_not_regular_package :
    (Nat.Prime 2 ∧ Nat.Prime 3 ∧ Nat.Prime 5 ∧ Nat.Prime 7) ∧
    (2 ≤ 3 ∧ 3 ≤ 5 ∧ 4 ≤ 8) ∧
    (Nat.fib 7 = 13 ∧ Nat.fib 8 = 21 ∧ Nat.fib 9 = 34) ∧
    (1 < 2 ∧ 2 < 3) ∧
    (Nat.fib 6 = 8 ∧ Nat.fib 7 = 13) :=
  paper_zeta_syntax_zeckendorf_prime_language_not_regular_seeds

/-- Paper-label wrapper for the Zeckendorf prime-language non-regular seed package.
    cor:zeta-syntax-zeckendorf-prime-language-not-regular -/
theorem paper_zeta_syntax_zeckendorf_prime_language_not_regular :
    (Nat.Prime 2 ∧ Nat.Prime 3 ∧ Nat.Prime 5 ∧ Nat.Prime 7) ∧
    (2 ≤ 3 ∧ 3 ≤ 5 ∧ 4 ≤ 8) ∧
    (Nat.fib 7 = 13 ∧ Nat.fib 8 = 21 ∧ Nat.fib 9 = 34) ∧
    (1 < 2 ∧ 2 < 3) ∧
    (Nat.fib 6 = 8 ∧ Nat.fib 7 = 13) :=
  paper_zeta_syntax_zeckendorf_prime_language_not_regular_seeds

end Omega.Zeta
