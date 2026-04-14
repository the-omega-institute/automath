import Mathlib.Tactic
import Mathlib.Data.Nat.Fib.Basic
import Omega.Zeta.LucasBarrier

/-! ### Lucas prime congruence and Wieferich fingerprint

This file verifies that for primes p ≤ 13, the Lucas number L_p ≡ 1 (mod p),
and defines the Wieferich fingerprint ν_p = v_p(L_p - 1). -/

namespace Omega.POM.LucasPrimeCongruence

open Omega.Zeta.LucasBarrier

/-! #### Key identity: L(n+1) = F(n) + F(n+2) -/

/-- Basic Lucas-Fibonacci relation: L(n) = F(n-1) + F(n+1) for n ≥ 1.
    lem:pom-lucas-modp -/
theorem lucas_eq_fib_sum (n : ℕ) :
    lucas n = Nat.fib (n - 1) + Nat.fib (n + 1) := by
  rfl

/-- L(n+1) = F(n) + F(n+2).
    lem:pom-lucas-modp -/
theorem lucas_succ_eq (n : ℕ) :
    lucas (n + 1) = Nat.fib n + Nat.fib (n + 2) := by
  simp [lucas]

/-! #### Seed verification: L_p ≡ 1 (mod p) for small primes -/

/-- L_2 ≡ 1 (mod 2).
    lem:pom-lucas-modp -/
theorem lucas_two_mod_two : lucas 2 % 2 = 1 := by
  unfold lucas; norm_num [Nat.fib_add_two]

/-- L_3 ≡ 1 (mod 3).
    lem:pom-lucas-modp -/
theorem lucas_three_mod_three : lucas 3 % 3 = 1 := by
  unfold lucas; norm_num [Nat.fib_add_two]

/-- L_5 ≡ 1 (mod 5).
    lem:pom-lucas-modp -/
theorem lucas_five_mod_five : lucas 5 % 5 = 1 := by
  unfold lucas; norm_num [Nat.fib_add_two]

/-- L_7 ≡ 1 (mod 7).
    lem:pom-lucas-modp -/
theorem lucas_seven_mod_seven : lucas 7 % 7 = 1 := by
  unfold lucas; norm_num [Nat.fib_add_two]

/-- L_11 ≡ 1 (mod 11).
    lem:pom-lucas-modp -/
theorem lucas_eleven_mod_eleven : lucas 11 % 11 = 1 := by
  unfold lucas; norm_num [Nat.fib_add_two]

/-- L_13 ≡ 1 (mod 13).
    lem:pom-lucas-modp -/
theorem lucas_thirteen_mod_thirteen : lucas 13 % 13 = 1 := by
  unfold lucas; norm_num [Nat.fib_add_two]

/-- Seed verification of L_p ≡ 1 (mod p) for all primes p ≤ 13.
    lem:pom-lucas-modp -/
theorem paper_lucas_prime_congruence_seeds :
    lucas 2 % 2 = 1 ∧ lucas 3 % 3 = 1 ∧ lucas 5 % 5 = 1 ∧
    lucas 7 % 7 = 1 ∧ lucas 11 % 11 = 1 ∧ lucas 13 % 13 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (unfold lucas; norm_num [Nat.fib_add_two])

/-- Lucas prime congruence for all primes in [2, 3, 5, 7, 11, 13].
    lem:pom-lucas-modp -/
theorem paper_pom_lucas_modp_seeds_list :
    (∀ p ∈ [2, 3, 5, 7, 11, 13], lucas p % p = 1) := by
  intro p hp
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (unfold lucas; norm_num [Nat.fib_add_two])

/-! #### Wieferich fingerprint ν_p -/

/-- The p-adic valuation of L_p - 1 for a prime p, measuring the
    "degeneracy strength" of the prime-length layer in the spectral gap.
    def:pom-lucas-nu-p -/
noncomputable def wieferichFingerprint (p : ℕ) : ℕ :=
  padicValNat p (lucas p - 1)

/-- ν_p ≥ 1 for small odd primes: p divides L_p - 1.
    def:pom-lucas-nu-p -/
theorem wieferich_divisibility_seeds :
    (lucas 3 - 1) % 3 = 0 ∧
    (lucas 5 - 1) % 5 = 0 ∧
    (lucas 7 - 1) % 7 = 0 ∧
    (lucas 11 - 1) % 11 = 0 ∧
    (lucas 13 - 1) % 13 = 0 := by
  unfold lucas; norm_num [Nat.fib_add_two]

end Omega.POM.LucasPrimeCongruence
