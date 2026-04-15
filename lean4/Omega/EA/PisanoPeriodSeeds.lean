import Mathlib.Data.Nat.Fib.Basic

/-!
# Pisano Period Seeds and Wall Theorem Seeds

Seed values for Fibonacci congruences: Nat.fib k % p = 0 for specific (k, p),
Wall's theorem divisibility witnesses, and minimality witnesses.
-/

namespace Omega.EA

/-! ## Pisano period seeds: fib(k) mod p = 0 -/

/-- fib(3) mod 2 = 0: F_3 = 2 is even.
    def:fib-congruence -/
theorem fib_mod_3_2 : Nat.fib 3 % 2 = 0 := by decide

/-- fib(8) mod 3 = 0: F_8 = 21, and 3 | 21.
    def:fib-congruence -/
theorem fib_mod_8_3 : Nat.fib 8 % 3 = 0 := by decide

/-- fib(10) mod 11 = 0: F_10 = 55, and 11 | 55.
    def:fib-congruence -/
theorem fib_mod_10_11 : Nat.fib 10 % 11 = 0 := by decide

/-- fib(16) mod 7 = 0: F_16 = 987, and 7 | 987.
    def:fib-congruence -/
theorem fib_mod_16_7 : Nat.fib 16 % 7 = 0 := by native_decide

/-- fib(20) mod 5 = 0: F_20 = 6765, and 5 | 6765.
    def:fib-congruence -/
theorem fib_mod_20_5 : Nat.fib 20 % 5 = 0 := by native_decide

/-! ## Wall theorem divisibility seeds: p | fib(k) with explicit witnesses -/

/-- 7 | fib(8): F_8 = 21 = 7 * 3.
    def:fib-congruence -/
theorem wall_seed_7_8 : Nat.fib 8 = 7 * 3 := by decide

/-- 11 | fib(10): F_10 = 55 = 11 * 5.
    def:fib-congruence -/
theorem wall_seed_11_10 : Nat.fib 10 = 11 * 5 := by decide

/-- 13 | fib(14): F_14 = 377 = 13 * 29.
    def:fib-congruence -/
theorem wall_seed_13_14 : Nat.fib 14 = 13 * 29 := by native_decide

/-! ## Minimality witnesses -/

/-- Minimality witness: fib(k) % 7 ≠ 0 for 1 ≤ k < 8.
    def:fib-congruence -/
theorem wall_minimal_7 :
    Nat.fib 1 % 7 ≠ 0 ∧ Nat.fib 2 % 7 ≠ 0 ∧ Nat.fib 3 % 7 ≠ 0 ∧
    Nat.fib 4 % 7 ≠ 0 ∧ Nat.fib 5 % 7 ≠ 0 ∧ Nat.fib 6 % 7 ≠ 0 ∧
    Nat.fib 7 % 7 ≠ 0 := by decide

/-- Minimality witness: fib(k) % 11 ≠ 0 for 1 ≤ k < 10.
    def:fib-congruence -/
theorem wall_minimal_11 :
    Nat.fib 1 % 11 ≠ 0 ∧ Nat.fib 2 % 11 ≠ 0 ∧ Nat.fib 3 % 11 ≠ 0 ∧
    Nat.fib 4 % 11 ≠ 0 ∧ Nat.fib 5 % 11 ≠ 0 ∧ Nat.fib 6 % 11 ≠ 0 ∧
    Nat.fib 7 % 11 ≠ 0 ∧ Nat.fib 8 % 11 ≠ 0 ∧ Nat.fib 9 % 11 ≠ 0 := by decide

/-- Minimality witness: fib(k) % 13 ≠ 0 for 1 ≤ k < 7.
    (Pisano period π(13) = 7, not 14; fib(7) = 13 is the first zero.)
    def:fib-congruence -/
theorem wall_minimal_13 :
    Nat.fib 1 % 13 ≠ 0 ∧ Nat.fib 2 % 13 ≠ 0 ∧ Nat.fib 3 % 13 ≠ 0 ∧
    Nat.fib 4 % 13 ≠ 0 ∧ Nat.fib 5 % 13 ≠ 0 ∧ Nat.fib 6 % 13 ≠ 0 := by decide

/-- 13 | fib(7): the actual minimal entry for 13.
    def:fib-congruence -/
theorem wall_seed_13_7 : Nat.fib 7 = 13 * 1 := by decide

/-- Pisano period seed package.
    def:fib-congruence -/
theorem paper_pisano_period_seeds :
    Nat.fib 3 % 2 = 0 ∧
    Nat.fib 8 % 3 = 0 ∧
    Nat.fib 10 % 11 = 0 ∧
    Nat.fib 16 % 7 = 0 ∧
    Nat.fib 20 % 5 = 0 :=
  ⟨fib_mod_3_2, fib_mod_8_3, fib_mod_10_11, fib_mod_16_7, fib_mod_20_5⟩

/-- Wall theorem seed package.
    def:fib-congruence -/
theorem paper_wall_seeds :
    Nat.fib 8 = 7 * 3 ∧
    Nat.fib 10 = 11 * 5 ∧
    Nat.fib 14 = 13 * 29 :=
  ⟨wall_seed_7_8, wall_seed_11_10, wall_seed_13_14⟩

end Omega.EA
