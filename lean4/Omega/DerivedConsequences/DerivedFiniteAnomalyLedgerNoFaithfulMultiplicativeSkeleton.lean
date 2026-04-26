import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic

namespace Omega.DerivedConsequences

theorem paper_derived_finite_anomaly_ledger_no_faithful_multiplicative_skeleton (e : ℕ → ℤ) :
    (∀ a b : ℕ, 1 <= a → 1 <= b → e (a * b) = e a + e b) →
      Function.Injective e → False := by
  intro hmul hinj
  have hone : e 1 = 0 := by
    have h11 := hmul 1 1 (by omega) (by omega)
    linarith
  have hpow :
      ∀ a n : ℕ, 1 ≤ a → e (a ^ n) = (n : ℤ) * e a := by
    intro a n ha
    induction n with
    | zero =>
        simp [hone]
    | succ n ih =>
        have hapos : 0 < a := lt_of_lt_of_le (by omega) ha
        have hpow_ge : 1 ≤ a ^ n := Nat.succ_le_of_lt (Nat.pow_pos hapos)
        rw [Nat.pow_succ, hmul (a ^ n) a hpow_ge ha, ih]
        calc
          (n : ℤ) * e a + e a = (n : ℤ) * e a + (1 : ℤ) * e a := by ring
          _ = ((n : ℤ) + 1) * e a := by ring
          _ = ((n + 1 : ℕ) : ℤ) * e a := by norm_num
  have he2_ne : e 2 ≠ 0 := by
    intro he2_zero
    have : 2 = 1 := hinj (by simpa [hone] using he2_zero)
    omega
  have he3_ne : e 3 ≠ 0 := by
    intro he3_zero
    have : 3 = 1 := hinj (by simpa [hone] using he3_zero)
    omega
  have h2_cases : e 2 < 0 ∨ 0 < e 2 := by omega
  have h3_cases : e 3 < 0 ∨ 0 < e 3 := by omega
  rcases h2_cases with h2_neg | h2_pos
  · rcases h3_cases with h3_neg | h3_pos
    · have hm_pos : 0 < Int.natAbs (e 3) := Int.natAbs_pos.mpr he3_ne
      have hn_pos : 0 < Int.natAbs (e 2) := Int.natAbs_pos.mpr he2_ne
      have hEqInt :
          e (2 ^ Int.natAbs (e 3)) = e (3 ^ Int.natAbs (e 2)) := by
        rw [hpow 2 (Int.natAbs (e 3)) (by omega), hpow 3 (Int.natAbs (e 2)) (by omega)]
        rw [Int.ofNat_natAbs_of_nonpos h3_neg.le, Int.ofNat_natAbs_of_nonpos h2_neg.le]
        ring
      have hEqNat : 2 ^ Int.natAbs (e 3) = 3 ^ Int.natAbs (e 2) := hinj hEqInt
      have hpow_inj :=
        Nat.Prime.pow_inj' Nat.prime_two Nat.prime_three (Nat.ne_of_gt hm_pos)
          (Nat.ne_of_gt hn_pos) hEqNat
      norm_num at hpow_inj
    · have hm_pos : 0 < Int.natAbs (e 3) := Int.natAbs_pos.mpr he3_ne
      have hn_pos : 0 < Int.natAbs (e 2) := Int.natAbs_pos.mpr he2_ne
      have hprod_zero :
          e (2 ^ Int.natAbs (e 3) * 3 ^ Int.natAbs (e 2)) = 0 := by
        have hleft : 1 ≤ 2 ^ Int.natAbs (e 3) := by
          exact Nat.succ_le_of_lt (Nat.pow_pos (by omega))
        have hright : 1 ≤ 3 ^ Int.natAbs (e 2) := by
          exact Nat.succ_le_of_lt (Nat.pow_pos (by omega))
        rw [hmul (2 ^ Int.natAbs (e 3)) (3 ^ Int.natAbs (e 2)) hleft hright]
        rw [hpow 2 (Int.natAbs (e 3)) (by omega), hpow 3 (Int.natAbs (e 2)) (by omega)]
        rw [Int.ofNat_natAbs_of_nonneg h3_pos.le, Int.ofNat_natAbs_of_nonpos h2_neg.le]
        ring
      have hEqNat : 2 ^ Int.natAbs (e 3) * 3 ^ Int.natAbs (e 2) = 1 := by
        apply hinj
        simpa [hone] using hprod_zero
      have hgt_one_left : 1 < 2 ^ Int.natAbs (e 3) := by
        exact Nat.one_lt_pow (Nat.ne_of_gt hm_pos) (by norm_num)
      have hgt_one :
          1 < 2 ^ Int.natAbs (e 3) * 3 ^ Int.natAbs (e 2) := by
        have hright_pos : 0 < 3 ^ Int.natAbs (e 2) := Nat.pow_pos (by omega)
        exact lt_of_lt_of_le hgt_one_left (Nat.le_mul_of_pos_right _ hright_pos)
      omega
  · rcases h3_cases with h3_neg | h3_pos
    · have hm_pos : 0 < Int.natAbs (e 3) := Int.natAbs_pos.mpr he3_ne
      have hn_pos : 0 < Int.natAbs (e 2) := Int.natAbs_pos.mpr he2_ne
      have hprod_zero :
          e (2 ^ Int.natAbs (e 3) * 3 ^ Int.natAbs (e 2)) = 0 := by
        have hleft : 1 ≤ 2 ^ Int.natAbs (e 3) := by
          exact Nat.succ_le_of_lt (Nat.pow_pos (by omega))
        have hright : 1 ≤ 3 ^ Int.natAbs (e 2) := by
          exact Nat.succ_le_of_lt (Nat.pow_pos (by omega))
        rw [hmul (2 ^ Int.natAbs (e 3)) (3 ^ Int.natAbs (e 2)) hleft hright]
        rw [hpow 2 (Int.natAbs (e 3)) (by omega), hpow 3 (Int.natAbs (e 2)) (by omega)]
        rw [Int.ofNat_natAbs_of_nonpos h3_neg.le, Int.ofNat_natAbs_of_nonneg h2_pos.le]
        ring
      have hEqNat : 2 ^ Int.natAbs (e 3) * 3 ^ Int.natAbs (e 2) = 1 := by
        apply hinj
        simpa [hone] using hprod_zero
      have hgt_one_left : 1 < 2 ^ Int.natAbs (e 3) := by
        exact Nat.one_lt_pow (Nat.ne_of_gt hm_pos) (by norm_num)
      have hgt_one :
          1 < 2 ^ Int.natAbs (e 3) * 3 ^ Int.natAbs (e 2) := by
        have hright_pos : 0 < 3 ^ Int.natAbs (e 2) := Nat.pow_pos (by omega)
        exact lt_of_lt_of_le hgt_one_left (Nat.le_mul_of_pos_right _ hright_pos)
      omega
    · have hm_pos : 0 < Int.natAbs (e 3) := Int.natAbs_pos.mpr he3_ne
      have hn_pos : 0 < Int.natAbs (e 2) := Int.natAbs_pos.mpr he2_ne
      have hEqInt :
          e (2 ^ Int.natAbs (e 3)) = e (3 ^ Int.natAbs (e 2)) := by
        rw [hpow 2 (Int.natAbs (e 3)) (by omega), hpow 3 (Int.natAbs (e 2)) (by omega)]
        rw [Int.ofNat_natAbs_of_nonneg h3_pos.le, Int.ofNat_natAbs_of_nonneg h2_pos.le]
        ring
      have hEqNat : 2 ^ Int.natAbs (e 3) = 3 ^ Int.natAbs (e 2) := hinj hEqInt
      have hpow_inj :=
        Nat.Prime.pow_inj' Nat.prime_two Nat.prime_three (Nat.ne_of_gt hm_pos)
          (Nat.ne_of_gt hn_pos) hEqNat
      norm_num at hpow_inj

end Omega.DerivedConsequences
