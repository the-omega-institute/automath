import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyCovarianceRecurrenceIntegersHankelRank3
import Omega.Folding.GaugeAnomalyTauIntClosed

namespace Omega.Folding

/-- Chapter-local wrapper for the rational power-spectrum formula of the gauge anomaly. The
fields record the closed covariance generating function, the value of `C₀`, the substitution of
`s` and `s⁻¹` into the two-sided covariance sum, the denominator-clearing step, and the final
rational/closed-form readout. -/
structure GaugeAnomalyPSDRationalData where
  covarianceGeneratingFunctionClosed : Prop
  covarianceZeroClosed : Prop
  substitutedLaurentSum : Prop
  denominatorsCleared : Prop
  psdIsRational : Prop
  psdClosedForm : Prop
  covarianceGeneratingFunctionClosed_h : covarianceGeneratingFunctionClosed
  covarianceZeroClosed_h : covarianceZeroClosed
  deriveSubstitutedLaurentSum :
    covarianceGeneratingFunctionClosed → covarianceZeroClosed → substitutedLaurentSum
  deriveDenominatorsCleared : substitutedLaurentSum → denominatorsCleared
  derivePsdIsRational : denominatorsCleared → psdIsRational
  derivePsdClosedForm : denominatorsCleared → psdClosedForm

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the rational closed form of the gauge-anomaly power spectral density.
    thm:fold-gauge-anomaly-psd-rational -/
theorem paper_fold_gauge_anomaly_psd_rational (D : GaugeAnomalyPSDRationalData) :
    D.psdIsRational ∧ D.psdClosedForm := by
  have hSum : D.substitutedLaurentSum :=
    D.deriveSubstitutedLaurentSum D.covarianceGeneratingFunctionClosed_h D.covarianceZeroClosed_h
  have hClear : D.denominatorsCleared := D.deriveDenominatorsCleared hSum
  exact ⟨D.derivePsdIsRational hClear, D.derivePsdClosedForm hClear⟩

end Omega.Folding
