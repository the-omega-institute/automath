import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

namespace Omega.Conclusion

open Filter

/-- Paper label: `thm:conclusion-gauge-anomaly-superpoisson-fano`. -/
theorem paper_conclusion_gauge_anomaly_superpoisson_fano
    (mean variance : ℕ → ℝ)
    (hmean : Tendsto (fun m : ℕ => mean m / (m : ℝ)) atTop (nhds ((4 : ℝ) / 9)))
    (hvar : Tendsto (fun m : ℕ => variance m / (m : ℝ)) atTop
      (nhds ((118 : ℝ) / 243)))
    (hmean_ne : ∀ᶠ m : ℕ in atTop, mean m ≠ 0) :
    Tendsto (fun m : ℕ => variance m / mean m) atTop (nhds ((59 : ℝ) / 54)) ∧
      (1 : ℝ) < (59 : ℝ) / 54 := by
  have hden_ne : ((4 : ℝ) / 9) ≠ 0 := by norm_num
  have hratio :
      Tendsto
        (fun m : ℕ => (variance m / (m : ℝ)) / (mean m / (m : ℝ))) atTop
        (nhds ((59 : ℝ) / 54)) := by
    have hdiv := hvar.div hmean hden_ne
    have hconst : ((118 : ℝ) / 243) / ((4 : ℝ) / 9) = (59 : ℝ) / 54 := by
      norm_num
    simpa [hconst] using hdiv
  have hquot_eq :
      (fun m : ℕ => (variance m / (m : ℝ)) / (mean m / (m : ℝ))) =ᶠ[atTop]
        fun m : ℕ => variance m / mean m := by
    filter_upwards [Filter.eventually_ge_atTop 1, hmean_ne] with m hm hmean_m
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hm_ne : (m : ℝ) ≠ 0 := hm_pos.ne'
    field_simp [hm_ne, hmean_m]
  exact ⟨Tendsto.congr' hquot_eq hratio, by norm_num⟩

end Omega.Conclusion
