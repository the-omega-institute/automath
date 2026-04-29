import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

namespace Omega.Conclusion

lemma conclusion_godel_five_symbol_threshold_log_arg_lower_bound :
    (1853659 / 8748000 : ℝ) ≤ Real.log (2 / ((1 + Real.sqrt 5) / 2)) := by
  set x : ℝ := Real.sqrt 5 - 2
  set y : ℝ := x / (x + 2)
  have hsqrt5_sq : (Real.sqrt 5) ^ 2 = (5 : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  have hsqrt5_pos : 0 < Real.sqrt 5 := by
    positivity
  have hsqrt5_nonneg : 0 ≤ Real.sqrt 5 := by
    positivity
  have hsqrt5_gt_two : (2 : ℝ) < Real.sqrt 5 := by
    nlinarith [hsqrt5_sq, hsqrt5_nonneg]
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    linarith
  have harg : 1 + x = 2 / ((1 + Real.sqrt 5) / 2) := by
    dsimp [x]
    field_simp [hsqrt5_pos.ne']
    nlinarith [hsqrt5_sq]
  have hy_eq : y = 1 - 2 / Real.sqrt 5 := by
    dsimp [y, x]
    field_simp [hsqrt5_pos.ne']
    ring
  have hsqrt5_gt_360_161 : (360 : ℝ) / 161 < Real.sqrt 5 := by
    have hbound_nonneg : 0 ≤ (360 : ℝ) / 161 := by
      positivity
    nlinarith [hsqrt5_sq, hbound_nonneg]
  have hy_lb : (19 / 180 : ℝ) ≤ y := by
    rw [hy_eq]
    have hdiv : (2 : ℝ) / Real.sqrt 5 ≤ (161 : ℝ) / 180 := by
      rw [div_le_iff₀ hsqrt5_pos]
      nlinarith [hsqrt5_gt_360_161]
    nlinarith
  let f : ℕ → ℝ := fun k => (2 : ℝ) * (1 / (2 * k + 1 : ℝ)) * y ^ (2 * k + 1)
  have hpartial :
      2 * y + (2 / 3 : ℝ) * y ^ 3 ≤ Real.log (1 + x) := by
    have hsum : Finset.sum (Finset.range 2) f ≤ Real.log (1 + x) := by
      exact
        sum_le_hasSum (Finset.range 2)
          (fun k _ => by
            have hy_nonneg : 0 ≤ y := by
              have : (0 : ℝ) ≤ 19 / 180 := by norm_num
              exact le_trans this hy_lb
            have hterm_nonneg :
                0 ≤ (2 : ℝ) * (1 / (2 * k + 1 : ℝ)) * y ^ (2 * k + 1) := by
              positivity
            simpa [f] using hterm_nonneg)
          (by simpa [f, y] using Real.hasSum_log_one_add hx_nonneg)
    have hsum' : 2 * y + 2 * ((2 + 1 : ℝ)⁻¹) * y ^ 3 ≤ Real.log (1 + x) := by
      simpa [f, Finset.sum_range_succ, y] using hsum
    nlinarith [hsum']
  have hrat_eq :
      (1853659 / 8748000 : ℝ) = 2 * (19 / 180 : ℝ) + (2 / 3 : ℝ) * (19 / 180 : ℝ) ^ 3 := by
    norm_num
  have hrat_le_partial : (1853659 / 8748000 : ℝ) ≤ 2 * y + (2 / 3 : ℝ) * y ^ 3 := by
    have hmono :
        2 * (19 / 180 : ℝ) + (2 / 3 : ℝ) * (19 / 180 : ℝ) ^ 3 ≤
          2 * y + (2 / 3 : ℝ) * y ^ 3 := by
      have hfactor :
          (2 * y + (2 / 3 : ℝ) * y ^ 3) -
              (2 * (19 / 180 : ℝ) + (2 / 3 : ℝ) * (19 / 180 : ℝ) ^ 3) =
            (y - 19 / 180) *
              ((2 / 3 : ℝ) *
                  (y ^ 2 + y * (19 / 180 : ℝ) + (19 / 180 : ℝ) ^ 2) +
                2) := by
        ring
      rw [← sub_nonneg, hfactor]
      have hy_diff_nonneg : 0 ≤ y - 19 / 180 := by
        linarith
      have hfactor_nonneg :
          0 ≤
            (2 / 3 : ℝ) * (y ^ 2 + y * (19 / 180 : ℝ) + (19 / 180 : ℝ) ^ 2) + 2 := by
        positivity
      exact mul_nonneg hy_diff_nonneg hfactor_nonneg
    simpa [hrat_eq] using hmono
  have : (1853659 / 8748000 : ℝ) ≤ Real.log (1 + x) :=
    le_trans hrat_le_partial hpartial
  simpa [harg] using this

/-- Paper label: `thm:conclusion-godel-five-symbol-threshold`. -/
theorem paper_conclusion_godel_five_symbol_threshold (M : ℕ) (hM : 2 ≤ M)
    (hbudget : Real.log (2 / ((1 + Real.sqrt 5) / 2)) / Real.log M ≤ (4 : ℝ) / 27) :
    5 ≤ M := by
  by_contra hnot
  have hMle4 : M ≤ 4 := by omega
  have hM_pos : 0 < (M : ℝ) := by
    have : 0 < M := by omega
    exact_mod_cast this
  have hM_one : (1 : ℝ) < M := by
    exact_mod_cast (show 1 < M by omega)
  have hM_le_four : (M : ℝ) ≤ 4 := by exact_mod_cast hMle4
  have hlogM_pos : 0 < Real.log (M : ℝ) := Real.log_pos hM_one
  have hlogM_le_log4 : Real.log (M : ℝ) ≤ Real.log (4 : ℝ) :=
    Real.log_le_log hM_pos hM_le_four
  have hlog4_eq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlog4_lt : Real.log (4 : ℝ) < (7 / 5 : ℝ) := by
    rw [hlog4_eq]
    nlinarith [Real.log_two_lt_d9]
  have hden_lt : Real.log (M : ℝ) < (7 / 5 : ℝ) :=
    lt_of_le_of_lt hlogM_le_log4 hlog4_lt
  have hnum_lb := conclusion_godel_five_symbol_threshold_log_arg_lower_bound
  have hq_pos : (0 : ℝ) < 1853659 / 8748000 := by norm_num
  have hmain :
      (4 : ℝ) / 27 <
        Real.log (2 / ((1 + Real.sqrt 5) / 2)) / Real.log (M : ℝ) := by
    calc
      (4 : ℝ) / 27 < (1853659 / 8748000 : ℝ) / (7 / 5 : ℝ) := by norm_num
      _ < (1853659 / 8748000 : ℝ) / Real.log (M : ℝ) := by
        exact div_lt_div_of_pos_left hq_pos hlogM_pos hden_lt
      _ ≤ Real.log (2 / ((1 + Real.sqrt 5) / 2)) / Real.log (M : ℝ) := by
        exact div_le_div_of_nonneg_right hnum_lb (le_of_lt hlogM_pos)
  linarith

end Omega.Conclusion
