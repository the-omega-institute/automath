import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

open Filter Topology

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-golden-lucas-hankel-inf5-anisotropy`. -/
theorem paper_conclusion_golden_lucas_hankel_inf5_anisotropy (logD v5D : ℕ → ℝ)
    (harch :
      Tendsto (fun q : ℕ => logD q / (q : ℝ) ^ 3) atTop
        (nhds ((1 / 3 : ℝ) * Real.log Real.goldenRatio)))
    (hv5 : Tendsto (fun q : ℕ => v5D q / (q : ℝ) ^ 2) atTop (nhds (3 / 4 : ℝ))) :
    Tendsto (fun q : ℕ => v5D q / logD q) atTop (nhds 0) := by
  have hlog_pos : 0 < Real.log Real.goldenRatio := Real.log_pos Real.one_lt_goldenRatio
  have harch_limit_ne : ((1 / 3 : ℝ) * Real.log Real.goldenRatio) ≠ 0 := by positivity
  have hquot :
      Tendsto
        (fun q : ℕ => (v5D q / (q : ℝ) ^ 2) / (logD q / (q : ℝ) ^ 3))
        atTop (nhds ((3 / 4 : ℝ) / ((1 / 3 : ℝ) * Real.log Real.goldenRatio))) := by
    exact hv5.div harch harch_limit_ne
  have hinv_q : Tendsto (fun q : ℕ => (1 : ℝ) / (q : ℝ)) atTop (nhds 0) := by
    simpa [one_div] using (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
  have hfactored :
      Tendsto
        (fun q : ℕ =>
          ((v5D q / (q : ℝ) ^ 2) / (logD q / (q : ℝ) ^ 3)) * (1 / (q : ℝ)))
        atTop (nhds 0) := by
    simpa using hquot.mul hinv_q
  have heventual :
      (fun q : ℕ => v5D q / logD q) =ᶠ[atTop]
        (fun q : ℕ =>
          ((v5D q / (q : ℝ) ^ 2) / (logD q / (q : ℝ) ^ 3)) * (1 / (q : ℝ))) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with q hq
    have hq_ne : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
    field_simp [hq_ne]
  exact hfactored.congr' heventual.symm

end Omega.Conclusion
