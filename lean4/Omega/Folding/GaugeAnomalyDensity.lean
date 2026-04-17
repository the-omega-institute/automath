import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyMean

namespace Omega.Folding

/-- A rational checkpoint matching the already verified `4/9` gauge-anomaly core. -/
theorem fold_gauge_anomaly_density_core_checkpoint : ((1 : ℚ) / 9 + 1 / 3) = 4 / 9 := by
  norm_num

end Omega.Folding
