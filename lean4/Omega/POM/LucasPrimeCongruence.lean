import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.ZMod.Basic
import Omega.Zeta.LucasBarrier

/-! ### Lucas prime congruence and Wieferich fingerprint

This file verifies that for primes p ≤ 13, the Lucas number L_p ≡ 1 (mod p),
and defines the Wieferich fingerprint ν_p = v_p(L_p - 1). -/

namespace Omega.POM.LucasPrimeCongruence

open Omega.Zeta.LucasBarrier
open scoped BigOperators

lemma pom_lucas_modp_fib_succ_eq_sum_range (n : ℕ) :
    Nat.fib (n + 1) = ∑ k ∈ Finset.range (n + 1), Nat.choose (n - k) k := by
  rw [Nat.fib_succ_eq_sum_choose]
  rw [← Finset.Nat.sum_antidiagonal_swap (f := fun p : ℕ × ℕ => Nat.choose p.1 p.2)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp

lemma pom_lucas_modp_pair_mul_eq (p k : ℕ) (hk0 : 0 < k) (hkp : k < p) :
    k * (Nat.choose (p - k) k + Nat.choose (p - k - 1) (k - 1)) =
      p * Nat.choose (p - k - 1) (k - 1) := by
  have hchoose := Nat.add_one_mul_choose_eq (p - k - 1) (k - 1)
  have hsucc : k = (k - 1) + 1 := by omega
  rw [← hsucc] at hchoose
  have hpk : p - k = (p - k - 1) + 1 := by omega
  rw [← hpk] at hchoose
  have hfirst :
      (p - k) * Nat.choose (p - k - 1) (k - 1) =
        Nat.choose (p - k) k * k := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hchoose
  calc
    k * (Nat.choose (p - k) k + Nat.choose (p - k - 1) (k - 1))
        = Nat.choose (p - k) k * k +
            k * Nat.choose (p - k - 1) (k - 1) := by ring
    _ = (p - k) * Nat.choose (p - k - 1) (k - 1) +
            k * Nat.choose (p - k - 1) (k - 1) := by rw [hfirst]
    _ = ((p - k) + k) * Nat.choose (p - k - 1) (k - 1) := by ring
    _ = p * Nat.choose (p - k - 1) (k - 1) := by
      rw [Nat.sub_add_cancel]
      omega

lemma pom_lucas_modp_pair_zmod_eq_zero (p k : ℕ) (hp : Nat.Prime p) (hk0 : 0 < k)
    (hkp : k < p) :
    ((Nat.choose (p - k) k + Nat.choose (p - k - 1) (k - 1) : ℕ) : ZMod p) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hk_ne_zero : (k : ZMod p) ≠ 0 := by
    intro hkz
    rw [ZMod.natCast_eq_zero_iff] at hkz
    exact (Nat.not_dvd_of_pos_of_lt hk0 hkp) hkz
  apply mul_left_cancel₀ hk_ne_zero
  rw [← Nat.cast_mul, pom_lucas_modp_pair_mul_eq p k hk0 hkp]
  simp

lemma pom_lucas_modp_cast_lucas_eq_pair_sum (p : ℕ) (hp2 : 2 ≤ p) :
    ((lucas p : ℕ) : ZMod p) =
      1 + ∑ k ∈ Finset.range (p - 1),
        ((Nat.choose (p - (k + 1)) (k + 1) +
            Nat.choose (p - (k + 1) - 1) k : ℕ) : ZMod p) := by
  have hplus :
      (Nat.fib (p + 1) : ZMod p) =
        ∑ k ∈ Finset.range (p + 1), ((Nat.choose (p - k) k : ℕ) : ZMod p) := by
    have h := congrArg (fun n : ℕ => (n : ZMod p))
      (pom_lucas_modp_fib_succ_eq_sum_range p)
    simpa using h
  have hminus :
      (Nat.fib (p - 1) : ZMod p) =
        ∑ k ∈ Finset.range (p - 1), ((Nat.choose (p - 2 - k) k : ℕ) : ZMod p) := by
    have h := congrArg (fun n : ℕ => (n : ZMod p))
      (pom_lucas_modp_fib_succ_eq_sum_range (p - 2))
    simpa [show p - 2 + 1 = p - 1 by omega] using h
  have hplus' :
      (∑ k ∈ Finset.range (p + 1), ((Nat.choose (p - k) k : ℕ) : ZMod p)) =
        1 + ∑ k ∈ Finset.range (p - 1),
          ((Nat.choose (p - (k + 1)) (k + 1) : ℕ) : ZMod p) := by
    rw [show p + 1 = p.succ by omega, Finset.sum_range_succ']
    rw [show p = (p - 1).succ by omega, Finset.sum_range_succ]
    have hlast : 0 < 1 + (p - 1) := by omega
    simp [add_comm, Nat.choose_eq_zero_of_lt hlast]
  rw [lucas, Nat.cast_add, hminus, hplus, hplus']
  rw [show
    (∑ k ∈ Finset.range (p - 1), ((Nat.choose (p - 2 - k) k : ℕ) : ZMod p)) +
        (1 + ∑ k ∈ Finset.range (p - 1),
          ((Nat.choose (p - (k + 1)) (k + 1) : ℕ) : ZMod p)) =
      1 + ((∑ k ∈ Finset.range (p - 1),
          ((Nat.choose (p - (k + 1)) (k + 1) : ℕ) : ZMod p)) +
        ∑ k ∈ Finset.range (p - 1), ((Nat.choose (p - 2 - k) k : ℕ) : ZMod p)) by
    abel]
  rw [← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hklt : k < p - 1 := Finset.mem_range.mp hk
  have hk2 : k + 2 ≤ p := by omega
  have hsub : p - (k + 1) - 1 = p - 2 - k := by omega
  rw [hsub]
  exact (Nat.cast_add _ _).symm

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

/-- Lucas prime congruence: for every prime `p`, `L_p ≡ 1 (mod p)`.
    lem:pom-lucas-modp -/
theorem paper_pom_lucas_modp (p : ℕ) (hp : Nat.Prime p) :
    Omega.Zeta.LucasBarrier.lucas p % p = 1 % p := by
  have hcast := pom_lucas_modp_cast_lucas_eq_pair_sum p hp.two_le
  have hsum_zero :
      (∑ k ∈ Finset.range (p - 1),
        (((Nat.choose (p - (k + 1)) (k + 1) : ℕ) : ZMod p) +
          ((Nat.choose (p - (k + 1) - 1) k : ℕ) : ZMod p))) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro k hk
    have hklt : k < p - 1 := Finset.mem_range.mp hk
    have hk0 : 0 < k + 1 := Nat.succ_pos k
    have hkp : k + 1 < p := by omega
    simpa [Nat.cast_add] using pom_lucas_modp_pair_zmod_eq_zero p (k + 1) hp hk0 hkp
  have hz : ((lucas p : ℕ) : ZMod p) = 1 := by
    simpa [hsum_zero] using hcast
  exact (ZMod.natCast_eq_natCast_iff' (lucas p) 1 p).mp (by simpa using hz)

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
