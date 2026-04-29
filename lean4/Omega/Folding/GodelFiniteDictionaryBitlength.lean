import Mathlib.Data.Nat.Size
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

namespace Omega.Folding

open scoped BigOperators

/-- The `n`-th prime, indexed from `0`. -/
noncomputable def nthPrime (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n

/-- Product of the first `T` primes. -/
noncomputable def primorial (T : ℕ) : ℕ :=
  ∏ t : Fin T, nthPrime t.1

/-- The finite-dictionary Gödel code with bounded exponents over the first `T` primes. -/
noncomputable def godelCode {T : ℕ} (a : Fin T → Nat) : ℕ :=
  ∏ t : Fin T, nthPrime t.1 ^ a t

/-- Base-2 bitlength proxy. -/
def bitLength (n : ℕ) : ℕ :=
  Nat.size n

lemma nthPrime_prime (n : ℕ) : Nat.Prime (nthPrime n) := by
  unfold nthPrime
  exact Nat.prime_nth_prime n

lemma nthPrime_pos (n : ℕ) : 0 < nthPrime n := by
  exact (nthPrime_prime n).pos

lemma nthPrime_one_le (n : ℕ) : 1 ≤ nthPrime n := by
  exact Nat.succ_le_of_lt (nthPrime_pos n)

lemma primorial_le_godelCode {B T : Nat} (a : Fin T → Nat)
    (ha : ∀ t, 1 ≤ a t ∧ a t ≤ B) : primorial T ≤ godelCode a := by
  classical
  unfold primorial godelCode
  refine Finset.prod_le_prod' ?_
  intro t ht
  have ht_one : 1 ≤ a t := (ha t).1
  calc
    nthPrime t.1 = nthPrime t.1 ^ 1 := by simp
    _ ≤ nthPrime t.1 ^ a t := by
      exact Nat.pow_le_pow_right (nthPrime_pos t.1) ht_one

lemma godelCode_le_primorial_pow {B T : Nat} (a : Fin T → Nat)
    (ha : ∀ t, 1 ≤ a t ∧ a t ≤ B) : godelCode a ≤ primorial T ^ B := by
  classical
  calc
    godelCode a = ∏ t : Fin T, nthPrime t.1 ^ a t := by rfl
    _ ≤ ∏ t : Fin T, nthPrime t.1 ^ B := by
      refine Finset.prod_le_prod' ?_
      intro t ht
      exact Nat.pow_le_pow_right (nthPrime_pos t.1) (ha t).2
    _ = primorial T ^ B := by
      rw [primorial, Finset.prod_pow]

lemma bitLength_mono {m n : ℕ} (h : m ≤ n) : bitLength m ≤ bitLength n := by
  unfold bitLength
  exact Nat.size_le_size h

lemma bitLength_pow_le (n B : Nat) (hB : 1 ≤ B) : bitLength (n ^ B) ≤ B * bitLength n := by
  unfold bitLength
  apply Nat.size_le.2
  have hlt : n ^ B < (2 ^ Nat.size n) ^ B := by
    have hB_pos : 0 < B := lt_of_lt_of_le (by decide : 0 < 1) hB
    exact Nat.pow_lt_pow_left (Nat.lt_size_self n) hB_pos.ne'
  have hEq : (2 ^ Nat.size n) ^ B = 2 ^ (B * Nat.size n) := by
    calc
      (2 ^ Nat.size n) ^ B = 2 ^ (Nat.size n * B) := by rw [Nat.pow_mul]
      _ = 2 ^ (B * Nat.size n) := by rw [Nat.mul_comm]
  exact hEq ▸ hlt

/-- Finite-dictionary Gödel coding is sandwiched between the primorial baseline and its `B`-th
power, and the same comparison yields the advertised bitlength bounds.
    cor:fold-godel-finite-dictionary-bitlength-theta-TlogT -/
theorem paper_fold_godel_finite_dictionary_bitlength_theta_tlogt (B T : Nat) (hB : 1 <= B)
    (a : Fin T -> Nat) (ha : ∀ t, 1 <= a t ∧ a t <= B) :
    primorial T <= godelCode a ∧ godelCode a <= primorial T ^ B ∧
      bitLength (primorial T) <= bitLength (godelCode a) ∧
      bitLength (godelCode a) <= B * bitLength (primorial T) := by
  have hlower : primorial T ≤ godelCode a := primorial_le_godelCode a ha
  have hupper : godelCode a ≤ primorial T ^ B := godelCode_le_primorial_pow a ha
  have hbitLower : bitLength (primorial T) ≤ bitLength (godelCode a) := bitLength_mono hlower
  have hbitUpperBase : bitLength (godelCode a) ≤ bitLength (primorial T ^ B) :=
    bitLength_mono hupper
  have hbitUpperPow : bitLength (primorial T ^ B) ≤ B * bitLength (primorial T) :=
    bitLength_pow_le (primorial T) B hB
  exact ⟨hlower, hupper, hbitLower, le_trans hbitUpperBase hbitUpperPow⟩

/-- Finite-dictionary Gödel coding is sandwiched between the primorial baseline and its `B`-th
power, and the same comparison yields the advertised bitlength bounds.
    cor:fold-godel-finite-dictionary-bitlength-theta-TlogT -/
theorem paper_fold_godel_finite_dictionary_bitlength_theta_TlogT (B T : Nat) (hB : 1 <= B)
    (a : Fin T -> Nat) (ha : ∀ t, 1 <= a t ∧ a t <= B) :
    primorial T <= godelCode a ∧ godelCode a <= primorial T ^ B ∧
      bitLength (primorial T) <= bitLength (godelCode a) ∧
      bitLength (godelCode a) <= B * bitLength (primorial T) + 1 := by
  obtain ⟨hlower, hupper, hbitLower, hbitUpper⟩ :=
    paper_fold_godel_finite_dictionary_bitlength_theta_tlogt B T hB a ha
  refine ⟨hlower, hupper, hbitLower, ?_⟩
  exact le_trans hbitUpper (Nat.le_add_right _ 1)

end Omega.Folding
