import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Omega.Folding.BernoulliPJordanCriticalScaling
import Omega.Folding.FoldBinRenyiRateCollapse

open Filter

namespace Omega.Conclusion

local notation "Filter.nhds" => nhds

/-- Paper label: `cor:conclusion-binfold-renyi-rate-collapse`. -/
theorem paper_conclusion_binfold_renyi_rate_collapse (q : ℝ) (hq : 0 < q) :
    Tendsto (Omega.Folding.foldBinRenyiEntropyRate q) Filter.atTop
      (Filter.nhds (Real.log Real.goldenRatio)) := by
  simpa using Omega.Folding.paper_fold_bin_renyi_rate_collapse q hq

end Omega.Conclusion
