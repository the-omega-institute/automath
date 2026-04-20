import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyCovarianceRecurrenceIntegersHankelRank3

namespace Omega.Folding

open Omega.Folding.AutocovarianceSeedValues

/-- Paper-facing normalized recurrence/Hankel package for the gauge-anomaly covariance sequence:
writing `d_k := Cov(g_t, g_{t+k})` for `k ≥ 1`, the cleared-denominator recurrence from
`paper_fold_gauge_anomaly_covariance_recurrence_integers_hankel_rank3` is equivalent to the
normalized order-three recurrence
`d_{k+3} = -(1/2)d_{k+2} + (1/4)d_{k+1} + (1/8)d_k`, and the same certificate gives
`rank(H) = 3`.
    thm:fold-gauge-anomaly-hankel-rank3 -/
theorem paper_fold_gauge_anomaly_hankel_rank3 (h : GaugeAnomalyAutocovarianceData) :
    (∀ k ≥ 1,
      autoCov (k + 3) =
        (-(1 / 2 : ℚ)) * autoCov (k + 2) + (1 / 4 : ℚ) * autoCov (k + 1) +
          (1 / 8 : ℚ) * autoCov k) ∧
      h.hankelRankEqThree := by
  rcases paper_fold_gauge_anomaly_covariance_recurrence_integers_hankel_rank3 h with
    ⟨hrec, _, _, hrank⟩
  refine ⟨?_, hrank⟩
  intro k hk
  have hkrec := hrec k hk
  linarith

end Omega.Folding
