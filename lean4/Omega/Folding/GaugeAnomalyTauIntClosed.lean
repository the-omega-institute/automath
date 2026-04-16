import Mathlib.Tactic
import Omega.Folding.AutocovarianceSeedValues

namespace Omega.Folding

open Omega.Folding.AutocovarianceSeedValues

/-- The variance seed `C₀` from the closed-form autocovariance law. -/
def gaugeAnomalyCovZero : ℚ :=
  20 / 81

/-- The geometric contribution `Σ_{k≥1} (1/8) (1/2)^k`. -/
def gaugeAnomalyTauGeomPiece : ℚ :=
  1 / 8

/-- The alternating geometric contribution `Σ_{k≥1} (7/648) (-1/2)^k`. -/
def gaugeAnomalyTauAltGeomPiece : ℚ :=
  -(7 / 1944)

/-- The arithmetico-geometric contribution `Σ_{k≥1} (k/108) (-1/2)^k`. -/
def gaugeAnomalyTauArithGeomPiece : ℚ :=
  -(1 / 486)

/-- The total autocovariance tail `Σ_{k≥1} C_k`. -/
def gaugeAnomalyCovTail : ℚ :=
  gaugeAnomalyTauGeomPiece + gaugeAnomalyTauAltGeomPiece + gaugeAnomalyTauArithGeomPiece

/-- The integrated autocorrelation time
`τ_int = 1 + (2 / C₀) Σ_{k≥1} C_k`. -/
def gaugeAnomalyTauInt : ℚ :=
  1 + (2 / gaugeAnomalyCovZero) * gaugeAnomalyCovTail

private theorem gaugeAnomalyCovZero_closed : gaugeAnomalyCovZero = (20 : ℚ) / 81 := by
  rfl

private theorem gaugeAnomalyCovTail_closed : gaugeAnomalyCovTail = (29 : ℚ) / 243 := by
  norm_num [gaugeAnomalyCovTail, gaugeAnomalyTauGeomPiece, gaugeAnomalyTauAltGeomPiece,
    gaugeAnomalyTauArithGeomPiece]

/-- Paper-facing wrapper for the exact integrated autocorrelation time of the gauge anomaly at the
critical point.
    prop:fold-gauge-anomaly-tau-int-closed -/
theorem paper_fold_gauge_anomaly_tau_int_closed : gaugeAnomalyTauInt = (59 : ℚ) / 30 := by
  rw [gaugeAnomalyTauInt, gaugeAnomalyCovZero_closed, gaugeAnomalyCovTail_closed]
  norm_num

end Omega.Folding
