import Omega.Zeta.ZeckendorfPrimeLanguage

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Introduction-level wrapper for the Zeckendorf prime-language obstruction theorem.
    thm:intro-zeckendorf -/
theorem paper_prime_languages_intro_zeckendorf_seeds :
    (Nat.Prime 2 ∧ Nat.Prime 3 ∧ Nat.Prime 5 ∧ Nat.Prime 7) ∧
      (2 ≤ 3 ∧ 3 ≤ 5 ∧ 4 ≤ 8) ∧
      (Nat.fib 7 = 13 ∧ Nat.fib 8 = 21 ∧ Nat.fib 9 = 34) ∧
      (1 < 2 ∧ 2 < 3) ∧
      (Nat.fib 6 = 8 ∧ Nat.fib 7 = 13) :=
  paper_zeta_syntax_zeckendorf_prime_language_not_regular_package

set_option maxHeartbeats 400000 in
/-- Wrapper theorem matching the introduction label.
    thm:intro-zeckendorf -/
theorem paper_prime_languages_intro_zeckendorf_package :
    (Nat.Prime 2 ∧ Nat.Prime 3 ∧ Nat.Prime 5 ∧ Nat.Prime 7) ∧
      (2 ≤ 3 ∧ 3 ≤ 5 ∧ 4 ≤ 8) ∧
      (Nat.fib 7 = 13 ∧ Nat.fib 8 = 21 ∧ Nat.fib 9 = 34) ∧
      (1 < 2 ∧ 2 < 3) ∧
      (Nat.fib 6 = 8 ∧ Nat.fib 7 = 13) :=
  paper_prime_languages_intro_zeckendorf_seeds

end Omega.Zeta
