import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Reverse-KL truncation depth lower bound

This file formalizes the logarithmic rearrangement of a geometric tail budget.
-/

namespace Omega.Zeta

/-- Logarithmic lower bound on the truncation depth forced by a geometric tail budget.
    prop:xi-reversekl-truncation-depth-lower-bound -/
theorem paper_xi_reversekl_truncation_depth_lower_bound (r epsilon b : ℝ) (N : ℕ)
    (hr0 : 0 < r) (hr1 : r < 1) (heps : 0 < epsilon) (hb : 0 < b)
    (hbudget : b ^ 2 * r ^ (2 * (N + 1)) / (1 - r ^ 2) ≤ epsilon) :
    (N : ℝ) ≥ Real.log (b ^ 2 / (epsilon * (1 - r ^ 2))) / (2 * |Real.log r|) - 1 := by
  have hr_nonneg : 0 ≤ r := le_of_lt hr0
  have hr_sq_lt_one : r ^ 2 < 1 := by
    simpa using pow_lt_one₀ hr_nonneg hr1 (by norm_num : (2 : ℕ) ≠ 0)
  have hden_pos : 0 < 1 - r ^ 2 := sub_pos.mpr hr_sq_lt_one
  have hb_sq_pos : 0 < b ^ 2 := sq_pos_of_pos hb
  have hA_pos : 0 < b ^ 2 / (epsilon * (1 - r ^ 2)) := by
    exact div_pos hb_sq_pos (mul_pos heps hden_pos)
  have hk_pos : 0 < r ^ (2 * (N + 1)) := pow_pos hr0 _
  have hbudget_den : b ^ 2 * r ^ (2 * (N + 1)) ≤ epsilon * (1 - r ^ 2) := by
    exact (div_le_iff₀ hden_pos).mp hbudget
  have hbudget_mul :
      b ^ 2 / (epsilon * (1 - r ^ 2)) * r ^ (2 * (N + 1)) ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (mul_pos heps hden_pos)]
    simpa [one_mul] using hbudget_den
  have hlog_le_zero :
      Real.log (b ^ 2 / (epsilon * (1 - r ^ 2))) +
          (2 * (N + 1) : ℝ) * Real.log r ≤ 0 := by
    have hprod_pos :
        0 < b ^ 2 / (epsilon * (1 - r ^ 2)) * r ^ (2 * (N + 1)) :=
      mul_pos hA_pos hk_pos
    have hlog_le := Real.log_le_log hprod_pos hbudget_mul
    rw [Real.log_mul hA_pos.ne' hk_pos.ne', Real.log_pow] at hlog_le
    norm_num at hlog_le
    simpa [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hlog_le
  have hlog_neg : Real.log r < 0 := (Real.log_neg_iff hr0).mpr hr1
  have hden_abs_pos : 0 < 2 * |Real.log r| := by
    exact mul_pos (by norm_num) (abs_pos.mpr hlog_neg.ne)
  have hmain :
      Real.log (b ^ 2 / (epsilon * (1 - r ^ 2))) ≤
        (2 * ((N : ℝ) + 1)) * |Real.log r| := by
    rw [abs_of_neg hlog_neg]
    nlinarith
  have hdiv :
      Real.log (b ^ 2 / (epsilon * (1 - r ^ 2))) / (2 * |Real.log r|) ≤
        (N : ℝ) + 1 := by
    rw [div_le_iff₀ hden_abs_pos]
    nlinarith
  linarith

end Omega.Zeta
