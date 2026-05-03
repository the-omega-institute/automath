import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Order.Field

namespace Omega.Conclusion

open Filter

/-- Paper label: `cor:conclusion-gauge-anomaly-selfaveraging-despite-superpoisson`. -/
theorem paper_conclusion_gauge_anomaly_selfaveraging_despite_superpoisson
    (mean variance : ℕ → ℝ)
    (hmean : Tendsto (fun m : ℕ => mean m / (m : ℝ)) atTop (nhds ((4 : ℝ) / 9)))
    (hvar : Tendsto (fun m : ℕ => variance m / (m : ℝ)) atTop
      (nhds ((118 : ℝ) / 243)))
    (hmean_pos : ∀ᶠ m : ℕ in atTop, 0 < mean m)
    (hvar_nonneg : ∀ᶠ m : ℕ in atTop, 0 ≤ variance m) :
    Tendsto (fun m : ℕ => (m : ℝ) * variance m / mean m ^ 2) atTop
      (nhds ((59 : ℝ) / 24)) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop,
        Real.sqrt (variance m) / mean m ≤ C / Real.sqrt (m : ℝ) := by
  have hmean_sq :
      Tendsto (fun m : ℕ => (mean m / (m : ℝ)) ^ 2) atTop
        (nhds (((4 : ℝ) / 9) ^ 2)) :=
    hmean.pow 2
  have hden_ne : (((4 : ℝ) / 9) ^ 2) ≠ 0 := by norm_num
  have hratio :
      Tendsto
        (fun m : ℕ => (variance m / (m : ℝ)) / (mean m / (m : ℝ)) ^ 2) atTop
        (nhds ((59 : ℝ) / 24)) := by
    have hdiv := hvar.div hmean_sq hden_ne
    have hconst : ((118 : ℝ) / 243) / (((4 : ℝ) / 9) ^ 2) = (59 : ℝ) / 24 := by
      norm_num
    simpa [hconst] using hdiv
  have hmain_eq :
      (fun m : ℕ => (variance m / (m : ℝ)) / (mean m / (m : ℝ)) ^ 2) =ᶠ[atTop]
        fun m : ℕ => (m : ℝ) * variance m / mean m ^ 2 := by
    filter_upwards [Filter.eventually_ge_atTop 1, hmean_pos] with m hm hmean_m
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hm_ne : (m : ℝ) ≠ 0 := hm_pos.ne'
    have hmean_ne : mean m ≠ 0 := hmean_m.ne'
    field_simp [hm_ne, hmean_ne, pow_two]
  have hlimit :
      Tendsto (fun m : ℕ => (m : ℝ) * variance m / mean m ^ 2) atTop
        (nhds ((59 : ℝ) / 24)) :=
    Tendsto.congr' hmain_eq hratio
  have hvar_lt_one :
      ∀ᶠ m : ℕ in atTop, variance m / (m : ℝ) < 1 :=
    hvar.eventually (gt_mem_nhds (by norm_num : (118 : ℝ) / 243 < 1))
  have hmean_gt :
      ∀ᶠ m : ℕ in atTop, (2 : ℝ) / 9 < mean m / (m : ℝ) :=
    hmean.eventually (lt_mem_nhds (by norm_num : (2 : ℝ) / 9 < (4 : ℝ) / 9))
  have hsqrt_bound :
      ∀ᶠ m : ℕ in atTop,
        Real.sqrt (variance m) / mean m ≤ ((9 : ℝ) / 2) / Real.sqrt (m : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 1, hvar_nonneg, hvar_lt_one, hmean_gt]
      with m hm hvar_m hvar_m_lt_one hmean_m_gt
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := hm_pos.le
    have hm_ne : (m : ℝ) ≠ 0 := hm_pos.ne'
    have hsqrtm_pos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm_pos
    have hsqrtm_ne : Real.sqrt (m : ℝ) ≠ 0 := hsqrtm_pos.ne'
    have hvar_div_nonneg : 0 ≤ variance m / (m : ℝ) := div_nonneg hvar_m hm_nonneg
    have hmean_div_pos : 0 < mean m / (m : ℝ) := by nlinarith
    have hmean_pos_m : 0 < mean m := by
      have hmul : 0 < (mean m / (m : ℝ)) * (m : ℝ) := mul_pos hmean_div_pos hm_pos
      simpa [div_mul_cancel₀ (mean m) hm_ne] using hmul
    have hsqrt_div_le_one : Real.sqrt (variance m / (m : ℝ)) ≤ 1 := by
      rw [Real.sqrt_le_one]
      exact le_of_lt hvar_m_lt_one
    have hratio_bound :
        Real.sqrt (variance m / (m : ℝ)) / (mean m / (m : ℝ)) ≤ (9 : ℝ) / 2 := by
      rw [div_le_iff₀ hmean_div_pos]
      nlinarith
    have hsqrt_var :
        Real.sqrt (variance m) =
          Real.sqrt (variance m / (m : ℝ)) * Real.sqrt (m : ℝ) := by
      have hdecomp : variance m = (variance m / (m : ℝ)) * (m : ℝ) := by
        field_simp [hm_ne]
      calc
        Real.sqrt (variance m) =
            Real.sqrt ((variance m / (m : ℝ)) * (m : ℝ)) := by
              nth_rewrite 1 [hdecomp]
              rfl
        _ = Real.sqrt (variance m / (m : ℝ)) * Real.sqrt (m : ℝ) := by
            rw [Real.sqrt_mul hvar_div_nonneg]
    have hrewrite :
        Real.sqrt (variance m) / mean m =
          (Real.sqrt (variance m / (m : ℝ)) / (mean m / (m : ℝ))) /
            Real.sqrt (m : ℝ) := by
      have hsqrt_sq : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt hm_nonneg
      rw [hsqrt_var]
      field_simp [hm_ne, hmean_pos_m.ne', hsqrtm_ne, hsqrt_sq, pow_two]
      rw [hsqrt_sq]
      ring
    rw [hrewrite]
    exact div_le_div_of_nonneg_right hratio_bound hsqrtm_pos.le
  exact ⟨hlimit, ⟨(9 : ℝ) / 2, by norm_num, hsqrt_bound⟩⟩

end Omega.Conclusion
