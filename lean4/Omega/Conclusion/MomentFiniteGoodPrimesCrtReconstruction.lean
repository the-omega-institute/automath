import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-moment-finite-good-primes-crt-reconstruction`.
Bounded integer representatives in `[-B, B]` that agree modulo a modulus larger than `2B`
are equal. This is the uniqueness core behind finite-prime CRT reconstruction. -/
theorem paper_conclusion_moment_finite_good_primes_crt_reconstruction
    (B M : ℕ) (hM : 2 * B < M) (x y : ℤ)
    (hx : -(B : ℤ) ≤ x ∧ x ≤ B) (hy : -(B : ℤ) ≤ y ∧ y ≤ B)
    (hcong : (M : ℤ) ∣ x - y) :
    x = y := by
  have hM_pos_nat : 0 < M := by omega
  have hM_pos_int : (0 : ℤ) < (M : ℤ) := by exact_mod_cast hM_pos_nat
  have hdiff_upper : x - y ≤ 2 * (B : ℤ) := by linarith [hx.2, hy.1]
  have hdiff_lower : -(2 * (B : ℤ)) ≤ x - y := by linarith [hx.1, hy.2]
  have habs_le : |x - y| ≤ 2 * (B : ℤ) := by
    exact abs_le.2 ⟨hdiff_lower, hdiff_upper⟩
  have hbound : 2 * (B : ℤ) < (M : ℤ) := by exact_mod_cast hM
  have habs_lt : |x - y| < (M : ℤ) := lt_of_le_of_lt habs_le hbound
  rcases hcong with ⟨k, hk⟩
  have hk_zero : k = 0 := by
    by_contra hk_ne
    have hk_abs_pos : (0 : ℤ) < |k| := abs_pos.mpr hk_ne
    have hk_abs_ge_one : (1 : ℤ) ≤ |k| := by omega
    have hM_le_mul : (M : ℤ) ≤ (M : ℤ) * |k| := by nlinarith
    have hM_le_abs : (M : ℤ) ≤ |x - y| := by
      calc
        (M : ℤ) ≤ (M : ℤ) * |k| := hM_le_mul
        _ = |(M : ℤ) * k| := by
          rw [abs_mul, abs_of_nonneg (le_of_lt hM_pos_int)]
        _ = |x - y| := by rw [hk]
    exact (not_lt_of_ge hM_le_abs) habs_lt
  have hzero : x - y = 0 := by simpa [hk_zero] using hk
  exact sub_eq_zero.mp hzero

end Omega.Conclusion
