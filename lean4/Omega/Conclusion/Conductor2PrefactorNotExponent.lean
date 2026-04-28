import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open Filter

/-- Paper label: `cor:conclusion-conductor2-prefactor-not-exponent`. -/
theorem paper_conclusion_conductor2_prefactor_not_exponent (D Dtilde : ℕ → ℝ) (φ c C : ℝ)
    (hφ : 1 < φ) (hc : 0 < c) (hC : 0 < C)
    (hDpos : ∀ᶠ m in Filter.atTop, 0 < D m)
    (hlim :
      Filter.Tendsto (fun m : ℕ => Real.log (D m) / (m : ℝ)) Filter.atTop
        (nhds ((1 / 2 : ℝ) * Real.log φ)))
    (hbound : ∀ᶠ m in Filter.atTop, c * D m ≤ Dtilde m ∧ Dtilde m ≤ C * D m) :
    Filter.Tendsto (fun m : ℕ => Real.log (Dtilde m) / (m : ℝ)) Filter.atTop
      (nhds ((1 / 2 : ℝ) * Real.log φ)) := by
  let _ := hφ
  have hlogc_div :
      Filter.Tendsto (fun m : ℕ => Real.log c / (m : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (Real.log c)
  have hlogC_div :
      Filter.Tendsto (fun m : ℕ => Real.log C / (m : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (Real.log C)
  have hlower_tendsto :
      Filter.Tendsto
        (fun m : ℕ => (Real.log c + Real.log (D m)) / (m : ℝ)) Filter.atTop
        (nhds ((1 / 2 : ℝ) * Real.log φ)) := by
    have hsum := hlogc_div.add hlim
    have heq :
        (fun m : ℕ => Real.log c / (m : ℝ) + Real.log (D m) / (m : ℝ)) =ᶠ[atTop]
          fun m : ℕ => (Real.log c + Real.log (D m)) / (m : ℝ) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with m hm
      have hm_ne : (m : ℝ) ≠ 0 := by positivity
      field_simp [hm_ne]
    exact Tendsto.congr' heq (by simpa using hsum)
  have hupper_tendsto :
      Filter.Tendsto
        (fun m : ℕ => (Real.log C + Real.log (D m)) / (m : ℝ)) Filter.atTop
        (nhds ((1 / 2 : ℝ) * Real.log φ)) := by
    have hsum := hlogC_div.add hlim
    have heq :
        (fun m : ℕ => Real.log C / (m : ℝ) + Real.log (D m) / (m : ℝ)) =ᶠ[atTop]
          fun m : ℕ => (Real.log C + Real.log (D m)) / (m : ℝ) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with m hm
      have hm_ne : (m : ℝ) ≠ 0 := by positivity
      field_simp [hm_ne]
    exact Tendsto.congr' heq (by simpa using hsum)
  have hlower :
      ∀ᶠ m in atTop,
        (Real.log c + Real.log (D m)) / (m : ℝ) ≤ Real.log (Dtilde m) / (m : ℝ) := by
    filter_upwards [hDpos, hbound, Filter.eventually_ge_atTop 1] with m hDm hbd hm
    have hcd_pos : 0 < c * D m := mul_pos hc hDm
    have htilde_pos : 0 < Dtilde m := lt_of_lt_of_le hcd_pos hbd.1
    have hlog : Real.log c + Real.log (D m) ≤ Real.log (Dtilde m) := by
      rw [← Real.log_mul (ne_of_gt hc) (ne_of_gt hDm)]
      exact Real.log_le_log hcd_pos hbd.1
    exact div_le_div_of_nonneg_right hlog (by positivity)
  have hupper :
      ∀ᶠ m in atTop,
        Real.log (Dtilde m) / (m : ℝ) ≤
          (Real.log C + Real.log (D m)) / (m : ℝ) := by
    filter_upwards [hDpos, hbound, Filter.eventually_ge_atTop 1] with m hDm hbd hm
    have hcd_pos : 0 < c * D m := mul_pos hc hDm
    have htilde_pos : 0 < Dtilde m := lt_of_lt_of_le hcd_pos hbd.1
    have hlog : Real.log (Dtilde m) ≤ Real.log C + Real.log (D m) := by
      rw [← Real.log_mul (ne_of_gt hC) (ne_of_gt hDm)]
      exact Real.log_le_log htilde_pos hbd.2
    exact div_le_div_of_nonneg_right hlog (by positivity)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower_tendsto hupper_tendsto hlower hupper

end Omega.Conclusion
