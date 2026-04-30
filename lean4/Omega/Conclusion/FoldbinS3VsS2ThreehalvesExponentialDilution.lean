import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

theorem paper_conclusion_foldbin_s3_vs_s2_threehalves_exponential_dilution
    {r2 r3 : ℝ} (hr2 : 0 < r2) (hr3 : 0 < r3)
    (h2lo : (2481 / 1000 : ℝ) < r2) (h3hi : r3 < (3087 / 1000 : ℝ)) :
    Real.log r3 - (3 / 2 : ℝ) * Real.log r2 < 0 := by
  have hpow : r3 ^ 2 < r2 ^ 3 := by
    have h3sq : r3 ^ 2 < (3087 / 1000 : ℝ) ^ 2 :=
      pow_lt_pow_left₀ h3hi hr3.le (by norm_num)
    have h2cube : (2481 / 1000 : ℝ) ^ 3 < r2 ^ 3 :=
      pow_lt_pow_left₀ h2lo (by norm_num) (by norm_num)
    have hnum : (3087 / 1000 : ℝ) ^ 2 < (2481 / 1000 : ℝ) ^ 3 := by
      norm_num
    exact h3sq.trans (hnum.trans h2cube)
  have hlog : Real.log (r3 ^ 2) < Real.log (r2 ^ 3) :=
    (Real.log_lt_log_iff (pow_pos hr3 2) (pow_pos hr2 3)).2 hpow
  have hlinear : 2 * Real.log r3 < 3 * Real.log r2 := by
    simpa [Real.log_pow] using hlog
  nlinarith

end Omega.Conclusion
