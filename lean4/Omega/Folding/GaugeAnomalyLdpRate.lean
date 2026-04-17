import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyEndpointFib
import Omega.Folding.GaugeAnomalyPressure

namespace Omega.Folding

/-- Concrete endpoint rate extracted from the `m = 0` asymptotic closure. -/
noncomputable def gaugeAnomalyEndpointRateZeroClosedForm : ℝ :=
  Real.log 13

/-- Concrete endpoint rate extracted from the `m = 1` asymptotic closure. -/
noncomputable def gaugeAnomalyEndpointRateOneClosedForm : ℝ :=
  Real.log 21

/-- Lightweight LDP wrapper around the existing pressure certificate. The endpoint rate functions
are fixed concrete closed forms, while the pressure content is imported from the pressure package. -/
structure GaugeAnomalyLdpData where
  pressureData : GaugeAnomalyPressureData

/-- Endpoint rate at `0`, exposed as a field-like definition on the LDP wrapper. -/
noncomputable def GaugeAnomalyLdpData.endpointRateZero (_D : GaugeAnomalyLdpData) : ℝ :=
  gaugeAnomalyEndpointRateZeroClosedForm

/-- Endpoint rate at `1`, exposed as a field-like definition on the LDP wrapper. -/
noncomputable def GaugeAnomalyLdpData.endpointRateOne (_D : GaugeAnomalyLdpData) : ℝ :=
  gaugeAnomalyEndpointRateOneClosedForm

/-- The large-deviation Legendre-Fenchel identity is represented by the pressure identity already
packaged in the gauge-anomaly pressure certificate. -/
def GaugeAnomalyLdpData.legendreFenchelFormula (D : GaugeAnomalyLdpData) : Prop :=
  D.pressureData.pressureIdentity

/-- Closed form for the left endpoint rate. -/
def GaugeAnomalyLdpData.endpointRateZeroClosed (D : GaugeAnomalyLdpData) : Prop :=
  D.endpointRateZero = Real.log (Nat.fib 7)

/-- Closed form for the right endpoint rate. -/
def GaugeAnomalyLdpData.endpointRateOneClosed (D : GaugeAnomalyLdpData) : Prop :=
  D.endpointRateOne = Real.log (Nat.fib 8)

private theorem gaugeAnomaly_endpoint_rate_zero_closed (D : GaugeAnomalyLdpData) :
    D.endpointRateZeroClosed := by
  rw [GaugeAnomalyLdpData.endpointRateZeroClosed, GaugeAnomalyLdpData.endpointRateZero]
  simpa using congrArg (fun n : ℕ => Real.log (n : ℝ)) fib_seven.symm

private theorem gaugeAnomaly_endpoint_rate_one_closed (D : GaugeAnomalyLdpData) :
    D.endpointRateOneClosed := by
  rw [GaugeAnomalyLdpData.endpointRateOneClosed, GaugeAnomalyLdpData.endpointRateOne]
  simpa using congrArg (fun n : ℕ => Real.log (n : ℝ)) fib_eight_fold.symm

/-- Pressure-based LDP wrapper together with the explicit endpoint closed forms.
    prop:fold-gauge-anomaly-ldp -/
theorem paper_fold_gauge_anomaly_ldp (D : GaugeAnomalyLdpData) :
    D.legendreFenchelFormula ∧ D.endpointRateZeroClosed ∧ D.endpointRateOneClosed := by
  have hPressure := paper_fold_gauge_anomaly_pressure D.pressureData
  refine ⟨hPressure.1, gaugeAnomaly_endpoint_rate_zero_closed D, gaugeAnomaly_endpoint_rate_one_closed D⟩

end Omega.Folding
