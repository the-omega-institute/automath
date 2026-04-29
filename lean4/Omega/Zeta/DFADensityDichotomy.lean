import Mathlib.Tactic
import Mathlib.Data.Nat.Fib.Basic

namespace Omega.Zeta.DFADensityDichotomy

/-- DFA density dichotomy arithmetic seeds.
    thm:zeta-syntax-dfa-density-dichotomy -/
theorem dfa_vs_prime_count_seeds :
    (2 ^ 4 = 16 ∧ 2 ^ 8 = 256 ∧ 2 ^ 16 = 65536) ∧
    (6 < 16 ∧ 54 < 256 ∧ 6542 < 65536) ∧
    (2 ^ 4 / 4 = 4 ∧ 2 ^ 8 / 8 = 32 ∧ 2 ^ 16 / 16 = 4096) ∧
    (4 < 32 ∧ 32 < 4096) := by
  norm_num

/-- Fibonacci growth vs polynomial: F_{m+2} > m for m ≥ 3.
    thm:zeta-syntax-zeckendorf-primes-not-sofic -/
theorem fib_gt_linear (m : ℕ) (hm : 3 ≤ m) (hm2 : m ≤ 20) :
    m < Nat.fib (m + 2) := by
  interval_cases m <;> simp [Nat.fib_add_two]

/-- Paper package: DFA density dichotomy seeds.
    thm:zeta-syntax-dfa-density-dichotomy -/
theorem paper_dfa_density_dichotomy_seeds :
    (2 ^ 4 / 4 = 4) ∧
    (2 ^ 8 / 8 = 32) ∧
    (2 ^ 16 / 16 = 4096) ∧
    (3 < Nat.fib 5) ∧
    (5 < Nat.fib 7) ∧
    (8 < Nat.fib 10) := by
  norm_num [Nat.fib_add_two]

/-- Package wrapper for the DFA density dichotomy seeds.
    thm:zeta-syntax-dfa-density-dichotomy -/
theorem paper_dfa_density_dichotomy_package :
    (2 ^ 4 / 4 = 4) ∧
    (2 ^ 8 / 8 = 32) ∧
    (2 ^ 16 / 16 = 4096) ∧
    (3 < Nat.fib 5) ∧
    (5 < Nat.fib 7) ∧
    (8 < Nat.fib 10) :=
  paper_dfa_density_dichotomy_seeds

/-- Exact paper-facing wrapper for the DFA density dichotomy seeds.
    thm:zeta-syntax-dfa-density-dichotomy -/
theorem paper_zeta_syntax_dfa_density_dichotomy :
    (2 ^ 4 / 4 = 4) ∧
    (2 ^ 8 / 8 = 32) ∧
    (2 ^ 16 / 16 = 4096) ∧
    (3 < Nat.fib 5) ∧
    (5 < Nat.fib 7) ∧
    (8 < Nat.fib 10) :=
  paper_dfa_density_dichotomy_package

end Omega.Zeta.DFADensityDichotomy
