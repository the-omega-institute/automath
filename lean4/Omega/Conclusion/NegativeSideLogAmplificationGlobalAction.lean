import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

lemma conclusion_negative_side_log_amplification_global_action_log_inv_div_mono
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≤ y) (hy_thin : y < Real.exp (-1)) :
    (1 / y) * Real.log (1 / y) ≤ (1 / x) * Real.log (1 / x) := by
  have hy_lt_one : y < 1 := by
    exact hy_thin.trans (Real.exp_lt_one_iff.mpr (by norm_num))
  have hy_le_one : y ≤ 1 := le_of_lt hy_lt_one
  have hone_le_inv_y : 1 ≤ 1 / y := by
    rw [one_div]
    exact (one_le_inv₀ hy).mpr hy_le_one
  have hlog_y_nonneg : 0 ≤ Real.log (1 / y) := Real.log_nonneg hone_le_inv_y
  have hinv_le : 1 / y ≤ 1 / x := by
    rw [one_div, one_div]
    exact (inv_le_inv₀ hy hx).mpr hxy
  have hlog_le : Real.log (1 / y) ≤ Real.log (1 / x) := by
    exact Real.log_le_log (by positivity) hinv_le
  exact mul_le_mul hinv_le hlog_le hlog_y_nonneg (by positivity)

/-- Paper label: `thm:conclusion-negative-side-log-amplification-global-action`. -/
theorem paper_conclusion_negative_side_log_amplification_global_action
    (A kappa h Ndet C : ℝ) (hA : 0 < A) (hkappa : 0 < kappa) (hh : 0 < h)
    (hC : 0 < C) (hthin : A / kappa < Real.exp (-1)) (hh_le : h ≤ A / kappa)
    (hN : C * (1 / h) * Real.log (1 / h) ≤ Ndet) :
    ∃ cMinus : ℝ,
      0 < cMinus ∧ cMinus * (kappa / A) * Real.log (kappa / A) ≤ Ndet := by
  refine ⟨C, hC, ?_⟩
  have hscale_pos : 0 < A / kappa := div_pos hA hkappa
  have hmono :
      (1 / (A / kappa)) * Real.log (1 / (A / kappa)) ≤
        (1 / h) * Real.log (1 / h) :=
    conclusion_negative_side_log_amplification_global_action_log_inv_div_mono hh hscale_pos
      hh_le hthin
  have hscaled :
      C * ((1 / (A / kappa)) * Real.log (1 / (A / kappa))) ≤
        C * ((1 / h) * Real.log (1 / h)) := by
    exact mul_le_mul_of_nonneg_left hmono (le_of_lt hC)
  have htarget :
      C * ((1 / (A / kappa)) * Real.log (1 / (A / kappa))) ≤ Ndet := by
    exact hscaled.trans (by simpa [mul_assoc] using hN)
  have hscale_eq : kappa / A = 1 / (A / kappa) := by
    field_simp [hA.ne', hkappa.ne']
  rw [hscale_eq, mul_assoc]
  exact htarget

end Omega.Conclusion
