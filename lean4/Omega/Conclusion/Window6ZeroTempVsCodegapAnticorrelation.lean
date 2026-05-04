import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-zero-temp-vs-codegap-anticorrelation`. -/
theorem paper_conclusion_window6_zero_temp_vs_codegap_anticorrelation :
    (∀ q : ℕ,
      let mass :=
        (2 : ℝ) ^ (q + 1) /
          (8 * (2 : ℝ) ^ q + 4 * (3 : ℝ) ^ q + 9 * (4 : ℝ) ^ q)
      mass ≤ (2 : ℝ) / (9 * (2 : ℝ) ^ q)) := by
  intro q
  dsimp
  have hden_pos :
      0 < 8 * (2 : ℝ) ^ q + 4 * (3 : ℝ) ^ q + 9 * (4 : ℝ) ^ q := by
    positivity
  have hrhs_den_pos : 0 < 9 * (2 : ℝ) ^ q := by
    positivity
  have hden_ge :
      9 * (4 : ℝ) ^ q ≤
        8 * (2 : ℝ) ^ q + 4 * (3 : ℝ) ^ q + 9 * (4 : ℝ) ^ q := by
    have hleft : 0 ≤ 8 * (2 : ℝ) ^ q := by positivity
    have hmid : 0 ≤ 4 * (3 : ℝ) ^ q := by positivity
    nlinarith
  have hpow : (4 : ℝ) ^ q = (2 : ℝ) ^ q * (2 : ℝ) ^ q := by
    rw [← mul_pow]
    norm_num
  have hcross :
      (2 : ℝ) ^ (q + 1) * (9 * (2 : ℝ) ^ q) ≤
        2 * (8 * (2 : ℝ) ^ q + 4 * (3 : ℝ) ^ q + 9 * (4 : ℝ) ^ q) := by
    calc
      (2 : ℝ) ^ (q + 1) * (9 * (2 : ℝ) ^ q)
          = 2 * (9 * (4 : ℝ) ^ q) := by
            rw [pow_succ, hpow]
            ring
      _ ≤ 2 * (8 * (2 : ℝ) ^ q + 4 * (3 : ℝ) ^ q + 9 * (4 : ℝ) ^ q) := by
        nlinarith
  exact (div_le_div_iff₀ hden_pos hrhs_den_pos).2 hcross

end Omega.Conclusion
