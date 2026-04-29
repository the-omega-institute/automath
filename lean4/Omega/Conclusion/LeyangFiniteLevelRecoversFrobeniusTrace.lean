import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-leyang-finite-level-recovers-frobenius-trace`.  A bounded
integer representative modulo `2^n` is unique once the interval width is strictly less than the
modulus. -/
theorem paper_conclusion_leyang_finite_level_recovers_frobenius_trace
    (n : ℕ) (a trA : ℤ) (B : ℕ)
    (hcong : ∃ k : ℤ, a - trA = k * (2 : ℤ) ^ n) (ha : |a| ≤ (B : ℤ))
    (hB : 2 * (B : ℤ) < (2 : ℤ) ^ n) :
    (∃ k : ℤ, a - trA = k * (2 : ℤ) ^ n) ∧
      ∀ b : ℤ, (∃ k : ℤ, b - trA = k * (2 : ℤ) ^ n) → |b| ≤ (B : ℤ) →
        b = a := by
  refine ⟨hcong, ?_⟩
  intro b hbcong hb
  rcases hcong with ⟨ka, hka⟩
  rcases hbcong with ⟨kb, hkb⟩
  have hdiff : b - a = (kb - ka) * (2 : ℤ) ^ n := by
    calc
      b - a = (b - trA) - (a - trA) := by ring
      _ = kb * (2 : ℤ) ^ n - ka * (2 : ℤ) ^ n := by rw [hkb, hka]
      _ = (kb - ka) * (2 : ℤ) ^ n := by ring
  have hpow_pos : 0 < (2 : ℤ) ^ n := pow_pos (by norm_num) n
  have hdiff_abs_lt : |b - a| < (2 : ℤ) ^ n := by
    have htriangle : |b - a| ≤ |b| + |a| := by
      calc
        |b - a| = |b + -a| := by ring_nf
        _ ≤ |b| + |-a| := abs_add_le b (-a)
        _ = |b| + |a| := by rw [abs_neg]
    have hsum_le : |b| + |a| ≤ 2 * (B : ℤ) := by omega
    exact lt_of_le_of_lt (le_trans htriangle hsum_le) hB
  have hcoeff_zero : kb - ka = 0 := by
    by_contra hcoeff_ne
    have hcoeff_abs_ge : (1 : ℤ) ≤ |kb - ka| := by
      have hcoeff_abs_pos : 0 < |kb - ka| := abs_pos.mpr hcoeff_ne
      omega
    have hpow_nonneg : 0 ≤ (2 : ℤ) ^ n := le_of_lt hpow_pos
    have hpow_le_abs : (2 : ℤ) ^ n ≤ |b - a| := by
      rw [hdiff, abs_mul, abs_of_nonneg hpow_nonneg]
      nlinarith [mul_le_mul_of_nonneg_right hcoeff_abs_ge hpow_nonneg]
    exact not_lt_of_ge hpow_le_abs hdiff_abs_lt
  have hsub_zero : b - a = 0 := by
    rw [hdiff, hcoeff_zero]
    ring
  omega

end Omega.Conclusion
