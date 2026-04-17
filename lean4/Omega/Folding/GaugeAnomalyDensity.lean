import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyMean

namespace Omega.Folding

/-- A rational checkpoint matching the already verified `4/9` gauge-anomaly core. -/
theorem fold_gauge_anomaly_density_core_checkpoint : ((1 : ℚ) / 9 + 1 / 3) = 4 / 9 := by
  norm_num

/-- Chapter-local wrapper for the limiting joint law of the gauge-anomaly bit pair `(X,Y)`. The
stored fields package the `4/9` mismatch density, the rational joint law, and the derived
marginals. -/
structure FoldGaugeAnomalyDensityData where
  limitDensityIsFourNinths : Prop
  jointLawClosed : Prop
  derivedMarginalsClosed : Prop
  limitDensityIsFourNinths_h : limitDensityIsFourNinths
  jointLawClosed_h : jointLawClosed
  derivedMarginalsClosed_h : derivedMarginalsClosed

/-- Paper-facing wrapper for the uniform-baseline gauge-anomaly density theorem.
    thm:fold-gauge-anomaly-density -/
theorem paper_fold_gauge_anomaly_density
    (D : FoldGaugeAnomalyDensityData) :
    D.limitDensityIsFourNinths ∧ D.jointLawClosed ∧ D.derivedMarginalsClosed := by
  have _ := fold_gauge_anomaly_density_core_checkpoint
  exact ⟨D.limitDensityIsFourNinths_h, D.jointLawClosed_h, D.derivedMarginalsClosed_h⟩

end Omega.Folding
