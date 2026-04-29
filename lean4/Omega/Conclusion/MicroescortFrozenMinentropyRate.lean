import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic

open Filter

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-microescort-frozen-minentropy-rate`. -/
theorem paper_conclusion_microescort_frozen_minentropy_rate
    (alpha_star g_star microRate : ℝ) (maxMicroMass K M : ℕ → ℝ)
    (hRate :
      Tendsto (fun m : ℕ => -Real.log (maxMicroMass m) / (m : ℝ)) atTop
        (nhds microRate))
    (hFrozen :
      Tendsto (fun m : ℕ => -Real.log (maxMicroMass m) / (m : ℝ)) atTop
        (nhds (alpha_star + g_star))) :
    microRate = alpha_star + g_star := by
  have _hK : ℕ → ℝ := K
  have _hM : ℕ → ℝ := M
  exact tendsto_nhds_unique hRate hFrozen

end Omega.Conclusion
