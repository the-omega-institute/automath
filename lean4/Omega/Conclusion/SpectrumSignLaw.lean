import Mathlib.Tactic

/-!
# Spectrum product sign law

The sign pattern (-1)^(q(q+1)/2) has period 4 in q.
-/

namespace Omega.Conclusion

/-- q*(q+1) is always even, so the natural division by 2 is exact. -/
private theorem mul_succ_even (q : ℕ) : 2 ∣ q * (q + 1) :=
  Nat.even_mul_succ_self q |>.two_dvd

/-- (-1)^(q(q+1)/2) has period 4.
    cor:conclusion-softcore-spectrum-product-sign-law -/
theorem neg_one_pow_triangular_mod4 (q : ℕ) :
    (-1 : ℤ) ^ (q * (q + 1) / 2) =
      if q % 4 = 0 ∨ q % 4 = 3 then 1 else -1 := by
  -- Suffices to show the result for q mod 4 shifted by multiples of 4
  -- Key: T(q+4) = T(q) + 2q + 10, and T(q+4) - T(q) is always even
  -- So (-1)^T(q+4) = (-1)^(T(q) + 2q + 10) and the sign depends only on T(q) mod 2
  induction q using Nat.strongRecOn with
  | _ q ih =>
    match q with
    | 0 => simp
    | 1 => simp
    | 2 => simp
    | 3 => simp
    | q + 4 =>
      -- T(q+4) = (q+4)(q+5)/2 = q(q+1)/2 + (2q+5)·2 - q(q+1)/2 ...
      -- Actually: (q+4)(q+5) = q(q+1) + 4(2q+5), so T(q+4) = T(q) + 2(2q+5)
      have heven : 2 ∣ q * (q + 1) := mul_succ_even q
      have hkey : (q + 4) * (q + 4 + 1) / 2 = q * (q + 1) / 2 + (4 * q + 10) := by
        have : (q + 4) * (q + 4 + 1) = q * (q + 1) + 2 * (4 * q + 10) := by ring
        omega
      rw [hkey, pow_add, ih q (by omega)]
      have : (-1 : ℤ) ^ (4 * q + 10) = 1 := by
        rw [show 4 * q + 10 = 2 * (2 * q + 5) from by ring, pow_mul, neg_one_sq, one_pow]
      rw [this, mul_one]
      have hmod : (q + 4) % 4 = q % 4 := by omega
      simp only [hmod]

/-- Spectrum sign law small values. cor:conclusion-softcore-spectrum-product-sign-law -/
theorem paper_spectrum_sign_law_package :
    (-1 : ℤ) ^ (0 * 1 / 2) = 1 ∧
    (-1 : ℤ) ^ (1 * 2 / 2) = -1 ∧
    (-1 : ℤ) ^ (2 * 3 / 2) = -1 ∧
    (-1 : ℤ) ^ (3 * 4 / 2) = 1 ∧
    (-1 : ℤ) ^ (4 * 5 / 2) = 1 ∧
    (-1 : ℤ) ^ (5 * 6 / 2) = -1 ∧
    (-1 : ℤ) ^ (6 * 7 / 2) = -1 ∧
    (-1 : ℤ) ^ (7 * 8 / 2) = 1 := by
  norm_num

/-- Spectrum sign = +1 when q ≡ 0 (mod 4).
    cor:conclusion-softcore-spectrum-product-sign-law -/
theorem neg_one_pow_triangular_q_mod4_zero (q : ℕ) (h : q % 4 = 0) :
    (-1 : ℤ) ^ (q * (q + 1) / 2) = 1 := by
  rw [neg_one_pow_triangular_mod4]
  simp [h]

/-- Spectrum sign = +1 when q ≡ 3 (mod 4).
    cor:conclusion-softcore-spectrum-product-sign-law -/
theorem neg_one_pow_triangular_q_mod4_three (q : ℕ) (h : q % 4 = 3) :
    (-1 : ℤ) ^ (q * (q + 1) / 2) = 1 := by
  rw [neg_one_pow_triangular_mod4]
  simp [h]

/-- Spectrum sign = -1 when q ≡ 1 (mod 4).
    cor:conclusion-softcore-spectrum-product-sign-law -/
theorem neg_one_pow_triangular_q_mod4_one (q : ℕ) (h : q % 4 = 1) :
    (-1 : ℤ) ^ (q * (q + 1) / 2) = -1 := by
  rw [neg_one_pow_triangular_mod4]
  simp [h]

/-- Spectrum sign = -1 when q ≡ 2 (mod 4).
    cor:conclusion-softcore-spectrum-product-sign-law -/
theorem neg_one_pow_triangular_q_mod4_two (q : ℕ) (h : q % 4 = 2) :
    (-1 : ℤ) ^ (q * (q + 1) / 2) = -1 := by
  rw [neg_one_pow_triangular_mod4]
  simp [h]

/-- Extended spectrum sign table q = 0..11.
    cor:conclusion-softcore-spectrum-product-sign-law -/
theorem paper_spectrum_sign_law_extended_table :
    (-1 : ℤ) ^ (0 * 1 / 2) = 1 ∧
    (-1 : ℤ) ^ (1 * 2 / 2) = -1 ∧
    (-1 : ℤ) ^ (2 * 3 / 2) = -1 ∧
    (-1 : ℤ) ^ (3 * 4 / 2) = 1 ∧
    (-1 : ℤ) ^ (4 * 5 / 2) = 1 ∧
    (-1 : ℤ) ^ (5 * 6 / 2) = -1 ∧
    (-1 : ℤ) ^ (6 * 7 / 2) = -1 ∧
    (-1 : ℤ) ^ (7 * 8 / 2) = 1 ∧
    (-1 : ℤ) ^ (8 * 9 / 2) = 1 ∧
    (-1 : ℤ) ^ (9 * 10 / 2) = -1 ∧
    (-1 : ℤ) ^ (10 * 11 / 2) = -1 ∧
    (-1 : ℤ) ^ (11 * 12 / 2) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-- Complete mod-4 case package for the spectrum sign law.
    cor:conclusion-softcore-spectrum-product-sign-law -/
theorem paper_spectrum_sign_mod4_case_package :
    (∀ q : ℕ, q % 4 = 0 → (-1 : ℤ) ^ (q * (q + 1) / 2) = 1) ∧
    (∀ q : ℕ, q % 4 = 1 → (-1 : ℤ) ^ (q * (q + 1) / 2) = -1) ∧
    (∀ q : ℕ, q % 4 = 2 → (-1 : ℤ) ^ (q * (q + 1) / 2) = -1) ∧
    (∀ q : ℕ, q % 4 = 3 → (-1 : ℤ) ^ (q * (q + 1) / 2) = 1) :=
  ⟨neg_one_pow_triangular_q_mod4_zero,
   neg_one_pow_triangular_q_mod4_one,
   neg_one_pow_triangular_q_mod4_two,
   neg_one_pow_triangular_q_mod4_three⟩

end Omega.Conclusion
