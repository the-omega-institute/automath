import Mathlib

namespace Omega.POM

private lemma hq_lower_endpoint_rewrite (q : ℕ) (hq : 2 ≤ q) :
    (q : ℝ) * Real.log 2 - Real.log (2 * (Real.sqrt Real.goldenRatio) ^ (q - 1)) =
      (((q - 1 : Nat) : ℝ) * Real.log (2 / Real.sqrt Real.goldenRatio)) := by
  have hq1 : 1 ≤ q := by omega
  have hsqrt_pos : 0 < Real.sqrt Real.goldenRatio := Real.sqrt_pos_of_pos Real.goldenRatio_pos
  have hsqrt_ne : Real.sqrt Real.goldenRatio ≠ 0 := ne_of_gt hsqrt_pos
  have hpow_pos : 0 < (Real.sqrt Real.goldenRatio) ^ (q - 1) := by positivity
  calc
    (q : ℝ) * Real.log 2 - Real.log (2 * (Real.sqrt Real.goldenRatio) ^ (q - 1))
        = (q : ℝ) * Real.log 2 -
            (Real.log 2 + Real.log ((Real.sqrt Real.goldenRatio) ^ (q - 1))) := by
          rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hpow_pos)]
    _ = (q : ℝ) * Real.log 2 -
          (Real.log 2 + (((q - 1 : Nat) : ℝ) * Real.log (Real.sqrt Real.goldenRatio))) := by
          rw [← Real.rpow_natCast, Real.log_rpow hsqrt_pos]
    _ = (((q - 1 : Nat) : ℝ) * (Real.log 2 - Real.log (Real.sqrt Real.goldenRatio))) := by
          rw [Nat.cast_sub hq1]
          norm_num
          ring
    _ = (((q - 1 : Nat) : ℝ) * Real.log (2 / Real.sqrt Real.goldenRatio)) := by
          rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hsqrt_ne]

private lemma hq_upper_endpoint_rewrite (q : ℕ) :
    (q : ℝ) * Real.log 2 - Real.log ((2 : ℝ) ^ q / Real.goldenRatio ^ (q - 1)) =
      (((q - 1 : Nat) : ℝ) * Real.log Real.goldenRatio) := by
  have htwo_pow_pos : 0 < (2 : ℝ) ^ q := by positivity
  have hphi_pow_pos : 0 < Real.goldenRatio ^ (q - 1) := by positivity
  calc
    (q : ℝ) * Real.log 2 - Real.log ((2 : ℝ) ^ q / Real.goldenRatio ^ (q - 1))
        = (q : ℝ) * Real.log 2 -
            (Real.log ((2 : ℝ) ^ q) - Real.log (Real.goldenRatio ^ (q - 1))) := by
          rw [Real.log_div (ne_of_gt htwo_pow_pos) (ne_of_gt hphi_pow_pos)]
    _ = (q : ℝ) * Real.log 2 -
          (((q : ℝ) * Real.log 2) - Real.log (Real.goldenRatio ^ (q - 1))) := by
          rw [← Real.rpow_natCast, Real.log_rpow (by norm_num : 0 < (2 : ℝ))]
    _ = Real.log (Real.goldenRatio ^ (q - 1)) := by ring
    _ = (((q - 1 : Nat) : ℝ) * Real.log Real.goldenRatio) := by
          rw [← Real.rpow_natCast, Real.log_rpow Real.goldenRatio_pos]

/-- Paper-facing package for the universal `r_q` and `h_q` bounds. The advertised `r_q` bounds
are the input hypotheses, and the `h_q` inequalities follow by unfolding `h_q` and applying
monotonicity of `Real.log` to the two-sided `r_q` squeeze.
    prop:pom-rq-universal-bounds -/
theorem paper_pom_rq_universal_bounds
    (rq hq : ℕ → ℝ)
    (hrqLower :
      ∀ q, 2 ≤ q → (2 : ℝ) ^ q / Real.goldenRatio ^ (q - 1) ≤ rq q)
    (hrqUpper :
      ∀ q, 2 ≤ q → rq q ≤ 2 * (Real.sqrt Real.goldenRatio) ^ (q - 1))
    (hhq : ∀ q, 2 ≤ q → hq q = q * Real.log 2 - Real.log (rq q)) :
    (∀ q, 2 ≤ q →
      (2 : ℝ) ^ q / Real.goldenRatio ^ (q - 1) ≤ rq q ∧
        rq q ≤ 2 * (Real.sqrt Real.goldenRatio) ^ (q - 1)) ∧
      (∀ q, 2 ≤ q →
        (((q - 1 : Nat) : ℝ) * Real.log (2 / Real.sqrt Real.goldenRatio) ≤ hq q) ∧
          hq q ≤ (((q - 1 : Nat) : ℝ) * Real.log Real.goldenRatio)) := by
  refine ⟨?_, ?_⟩
  · intro q hq_ge
    exact ⟨hrqLower q hq_ge, hrqUpper q hq_ge⟩
  · intro q hq_ge
    have hrq_lower := hrqLower q hq_ge
    have hrq_upper := hrqUpper q hq_ge
    have hlower_pos : 0 < (2 : ℝ) ^ q / Real.goldenRatio ^ (q - 1) := by positivity
    have hrq_pos : 0 < rq q := lt_of_lt_of_le hlower_pos hrq_lower
    have hlog_upper :
        Real.log (rq q) ≤ Real.log (2 * (Real.sqrt Real.goldenRatio) ^ (q - 1)) :=
      Real.log_le_log hrq_pos hrq_upper
    have hlog_lower :
        Real.log ((2 : ℝ) ^ q / Real.goldenRatio ^ (q - 1)) ≤ Real.log (rq q) :=
      Real.log_le_log hlower_pos hrq_lower
    refine ⟨?_, ?_⟩
    · rw [hhq q hq_ge]
      have hbound :
          (q : ℝ) * Real.log 2 - Real.log (2 * (Real.sqrt Real.goldenRatio) ^ (q - 1)) ≤
            (q : ℝ) * Real.log 2 - Real.log (rq q) := by
        linarith
      rw [← hq_lower_endpoint_rewrite q hq_ge]
      exact hbound
    · rw [hhq q hq_ge]
      have hbound :
          (q : ℝ) * Real.log 2 - Real.log (rq q) ≤
            (q : ℝ) * Real.log 2 - Real.log ((2 : ℝ) ^ q / Real.goldenRatio ^ (q - 1)) := by
        linarith
      rw [← hq_upper_endpoint_rewrite q]
      exact hbound

end Omega.POM
