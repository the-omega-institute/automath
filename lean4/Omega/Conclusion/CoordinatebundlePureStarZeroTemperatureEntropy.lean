import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-coordinatebundle-pure-star-zero-temperature-entropy`. -/
theorem paper_conclusion_coordinatebundle_pure_star_zero_temperature_entropy (m n s : ℕ)
    (hs : 0 < s) (hsn : s ≤ n) :
    Real.log (((2 : ℝ) * (s : ℝ) * (2 : ℝ) ^ (m * (s - 1))) ^
          (2 ^ (m * (n - s)))) /
        ((2 : ℝ) ^ (m * (n - s))) =
      Real.log ((2 : ℝ) * (s : ℝ)) + (((m * (s - 1) : ℕ) : ℝ) * Real.log 2) := by
  have _hsn_used := hsn
  have hbase_ne :
      (2 : ℝ) * (s : ℝ) * (2 : ℝ) ^ (m * (s - 1)) ≠ 0 := by
    positivity
  have hden_ne : (2 : ℝ) ^ (m * (n - s)) ≠ 0 := by positivity
  rw [Real.log_pow, Nat.cast_pow, Nat.cast_ofNat]
  rw [mul_div_cancel_left₀ _ hden_ne]
  rw [Real.log_mul (by positivity : (2 : ℝ) * (s : ℝ) ≠ 0)
    (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))]
  rw [Real.log_pow]

end Omega.Conclusion
