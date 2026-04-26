import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Ring.Basic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-gauge-anomaly-l2-law`. -/
theorem paper_conclusion_gauge_anomaly_l2_law (mean variance l2Error : ℕ → ℝ)
    (hmean : Filter.Tendsto mean Filter.atTop (nhds (4 / 9 : ℝ)))
    (hvar : Filter.Tendsto variance Filter.atTop (nhds 0))
    (hl2 : ∀ m, l2Error m = variance m + (mean m - 4 / 9) ^ 2) :
    Filter.Tendsto l2Error Filter.atTop (nhds 0) := by
  have hcentered :
      Filter.Tendsto (fun m => mean m - 4 / 9) Filter.atTop (nhds (0 : ℝ)) := by
    simpa [sub_self] using
      hmean.sub
        (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℕ => (4 / 9 : ℝ)) Filter.atTop (nhds (4 / 9 : ℝ)))
  have hsquare :
      Filter.Tendsto (fun m => (mean m - 4 / 9) ^ 2) Filter.atTop (nhds (0 : ℝ)) := by
    simpa using hcentered.pow 2
  have hsum :
      Filter.Tendsto (fun m => variance m + (mean m - 4 / 9) ^ 2) Filter.atTop
        (nhds (0 : ℝ)) := by
    simpa using hvar.add hsquare
  exact hsum.congr' (Filter.Eventually.of_forall fun m => (hl2 m).symm)

end Omega.Conclusion
