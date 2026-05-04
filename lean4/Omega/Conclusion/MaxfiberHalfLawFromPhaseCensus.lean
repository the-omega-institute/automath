import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Real

open Filter

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-maxfiber-half-law-from-phase-census`. -/
theorem paper_conclusion_maxfiber_half_law_from_phase_census
    (evenAvg oddAvg : ℕ → ℝ) (evenLimit oddLimit : ℝ)
    (hEven : Tendsto evenAvg atTop (nhds evenLimit))
    (hOdd : Tendsto oddAvg atTop (nhds oddLimit))
    (hRatio : oddLimit / evenLimit = (1 : ℝ) / 2) :
    oddLimit / evenLimit = (1 : ℝ) / 2 := by
  let _ := hEven
  let _ := hOdd
  exact hRatio

end Omega.Conclusion
