import Mathlib.Tactic
import Omega.Folding.AutocovarianceSeedValues

namespace Omega

/-- Paper-facing closed form for the gauge-anomaly autocovariance, reindexed to start at `k = 1`.
    thm:fold-gauge-anomaly-cov-closed -/
theorem paper_fold_gauge_anomaly_cov_closed (k : Nat) :
    Omega.Folding.AutocovarianceSeedValues.autoCov (k + 1) =
      (1 / 16 : ℚ) * (1 / 2 : ℚ) ^ k +
        ((-13 : ℚ) / 1296 - k / 216) * ((-1 : ℚ) / 2) ^ k := by
  simp [Omega.Folding.AutocovarianceSeedValues.autoCov]
  ring

end Omega
