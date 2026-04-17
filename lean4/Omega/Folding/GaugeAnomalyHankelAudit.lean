import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyCovarianceRecurrenceIntegersHankelRank3

namespace Omega.Folding

open Omega.Folding.AutocovarianceSeedValues

/-- Paper-facing audit corollary: the autocovariance sequence satisfies the integer recurrence, and
the same data carries the exact Hankel-rank-three certificate. -/
theorem paper_fold_gauge_anomaly_hankel_audit (h : GaugeAnomalyAutocovarianceData) :
    (∀ k ≥ 1, 8 * autoCov (k + 3) + 4 * autoCov (k + 2) - 2 * autoCov (k + 1) - autoCov k = 0) ∧
      h.hankelRankEqThree := by
  rcases paper_fold_gauge_anomaly_covariance_recurrence_integers_hankel_rank3 h with
    ⟨hrec, _, _, hrank⟩
  exact ⟨hrec, hrank⟩

end Omega.Folding
