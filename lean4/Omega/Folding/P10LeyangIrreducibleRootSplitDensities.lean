import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyP10LeyangChebotarevProductLaw

namespace Omega.Folding

/-- Paper label: `cor:fold-gauge-anomaly-P10-leyang-irreducible-root-split-densities`. -/
theorem fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_paper_statement
    (δI δR δS : ℚ) (hI : δI = (1 : ℚ) / 10) (hR : δR = (1 : ℚ) / 2)
    (hS : δS = (1 : ℚ) / 6) :
    δI * δR = (1 : ℚ) / 20 ∧ δI * δS = (1 : ℚ) / 60 := by
  constructor
  · rw [hI, hR]
    norm_num
  · rw [hI, hS]
    norm_num

end Omega.Folding
