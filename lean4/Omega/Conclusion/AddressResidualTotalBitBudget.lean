import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-address-residual-total-bit-budget`. -/
theorem paper_conclusion_address_residual_total_bit_budget (T m : ℕ) {R : Type*} [Fintype R]
    {c : ℝ} (hT : 2 ≤ T) (hc : 0 < c)
    (hCap : c * (T : ℝ)^2 * Real.log (T : ℝ) / (2 : ℝ)^m ≤ (Fintype.card R : ℝ)) :
    (m : ℝ) + Real.log (Fintype.card R : ℝ) / Real.log 2 ≥
      2 * Real.log (T : ℝ) / Real.log 2 + Real.log (Real.log (T : ℝ)) / Real.log 2 +
        Real.log c / Real.log 2 := by
  have hTgt1 : 1 < (T : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (show (1 : ℕ) < 2 by decide) hT
  have hTpos : 0 < (T : ℝ) := lt_trans zero_lt_one hTgt1
  have hlogT_pos : 0 < Real.log (T : ℝ) := Real.log_pos hTgt1
  have hpow_pos : 0 < (2 : ℝ)^m := by positivity
  have hnum_pos : 0 < c * (T : ℝ)^2 * Real.log (T : ℝ) := by positivity
  have hleft_pos : 0 < c * (T : ℝ)^2 * Real.log (T : ℝ) / (2 : ℝ)^m := by
    exact div_pos hnum_pos hpow_pos
  have hcard_pos : 0 < (Fintype.card R : ℝ) := lt_of_lt_of_le hleft_pos hCap
  have hlog :=
    Real.log_le_log hleft_pos hCap
  have hlog_expand :
      Real.log (c * (T : ℝ)^2 * Real.log (T : ℝ) / (2 : ℝ)^m) =
        Real.log c + 2 * Real.log (T : ℝ) + Real.log (Real.log (T : ℝ)) -
          (m : ℝ) * Real.log 2 := by
    have hlog_pow_T : Real.log ((T : ℝ)^2) = 2 * Real.log (T : ℝ) := by
      rw [← Real.rpow_natCast, Real.log_rpow hTpos]
      norm_num
    have hlog_pow_2 : Real.log ((2 : ℝ)^m) = (m : ℝ) * Real.log 2 := by
      rw [← Real.rpow_natCast, Real.log_rpow (show 0 < (2 : ℝ) by norm_num)]
    rw [Real.log_div hnum_pos.ne' (pow_ne_zero _ (show (2 : ℝ) ≠ 0 by norm_num))]
    rw [mul_assoc, Real.log_mul hc.ne' (mul_ne_zero (pow_ne_zero _ hTpos.ne') hlogT_pos.ne')]
    rw [Real.log_mul (pow_ne_zero _ hTpos.ne') hlogT_pos.ne']
    rw [hlog_pow_T, hlog_pow_2]
    ring
  have hbase :
      Real.log c + 2 * Real.log (T : ℝ) + Real.log (Real.log (T : ℝ)) ≤
        (m : ℝ) * Real.log 2 + Real.log (Fintype.card R : ℝ) := by
    rw [hlog_expand] at hlog
    linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hbits :
      (Real.log c + 2 * Real.log (T : ℝ) + Real.log (Real.log (T : ℝ))) / Real.log 2 ≤
        (m : ℝ) + Real.log (Fintype.card R : ℝ) / Real.log 2 := by
    refine (div_le_iff₀ hlog2_pos).2 ?_
    calc
      Real.log c + 2 * Real.log (T : ℝ) + Real.log (Real.log (T : ℝ)) ≤
          (m : ℝ) * Real.log 2 + Real.log (Fintype.card R : ℝ) := hbase
      _ = ((m : ℝ) + Real.log (Fintype.card R : ℝ) / Real.log 2) * Real.log 2 := by
        field_simp [ne_of_gt hlog2_pos]
  have hsplit :
      (Real.log c + 2 * Real.log (T : ℝ) + Real.log (Real.log (T : ℝ))) / Real.log 2 =
        2 * Real.log (T : ℝ) / Real.log 2 + Real.log (Real.log (T : ℝ)) / Real.log 2 +
          Real.log c / Real.log 2 := by
    field_simp [ne_of_gt hlog2_pos]
    ring
  calc
    (m : ℝ) + Real.log (Fintype.card R : ℝ) / Real.log 2 ≥
        (Real.log c + 2 * Real.log (T : ℝ) + Real.log (Real.log (T : ℝ))) / Real.log 2 := hbits
    _ = 2 * Real.log (T : ℝ) / Real.log 2 + Real.log (Real.log (T : ℝ)) / Real.log 2 +
        Real.log c / Real.log 2 := hsplit

end Omega.Conclusion
