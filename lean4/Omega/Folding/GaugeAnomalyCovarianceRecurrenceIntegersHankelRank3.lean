import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyHankelJordanCertificate

namespace Omega.Folding

open Omega.Folding.AutocovarianceSeedValues

/-- Paper-facing recurrence/Hankel package for the gauge-anomaly covariance sequence: clearing
denominators in the closed-form recurrence yields the integer relation
`8 C_{k+3} + 4 C_{k+2} - 2 C_{k+1} - C_k = 0`, and the existing Hankel certificate shows that the
infinite Hankel matrix has rank exactly `3`.
    prop:fold-gauge-anomaly-covariance-recurrence-integers-hankel-rank3 -/
theorem paper_fold_gauge_anomaly_covariance_recurrence_integers_hankel_rank3
    (h : GaugeAnomalyAutocovarianceData) :
    (∀ k ≥ 1, 8 * autoCov (k + 3) + 4 * autoCov (k + 2) - 2 * autoCov (k + 1) - autoCov k = 0) ∧
      h.hankelDet3Nonzero ∧ h.hankelDet4Zero ∧ h.hankelRankEqThree := by
  rcases GaugeAnomalyAutocovarianceData.paper_fold_gauge_anomaly_hankel_jordan_certificate h with
      ⟨h3, h4, hrank⟩
  refine ⟨?_, h3, h4, hrank⟩
  intro k hk
  simp [autoCov]
  ring

end Omega.Folding
