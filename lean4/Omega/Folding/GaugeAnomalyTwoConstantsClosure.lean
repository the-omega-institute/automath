import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyGcDefectFarfieldExpansion
import Omega.Folding.GaugeAnomalyGcDefectSign
import Omega.Folding.GaugeAnomalyLdpRate
import Omega.Folding.GaugeAnomalyPressureCumulants5

namespace Omega.Folding

/-- Concrete pressure witness used to instantiate the lightweight LDP wrapper. -/
def fold_gauge_anomaly_two_constants_closure_pressure_data : GaugeAnomalyPressureData where
  adjacencyCertificate := True
  perronBranchQuarticCertificate := True
  pressureIdentity := True
  firstDerivativeClosed := True
  secondDerivativeClosed := True
  thirdDerivativeClosed := True
  hasAdjacencyCertificate := trivial
  derivePerronBranchQuarticCertificate := by
    intro _
    trivial
  derivePressureIdentity := by
    intro _
    trivial
  deriveFirstDerivativeClosed := by
    intro _
    trivial
  deriveSecondDerivativeClosed := by
    intro _
    trivial
  deriveThirdDerivativeClosed := by
    intro _
    trivial

/-- Concrete LDP witness packaging the audited endpoint closed forms. -/
def fold_gauge_anomaly_two_constants_closure_ldp_data : GaugeAnomalyLdpData where
  pressureData := fold_gauge_anomaly_two_constants_closure_pressure_data

/-- Explicit cumulant profile through order five. -/
def fold_gauge_anomaly_two_constants_closure_kappa : ℕ → ℚ
  | 1 => 4 / 9
  | 2 => 118 / 243
  | 3 => -1174 / 2187
  | 4 => -8890 / 19683
  | 5 => 17294570 / 1594323
  | _ => 0

/-- Concrete cumulant witness used to read off the odd cubic Taylor truncation. -/
def fold_gauge_anomaly_two_constants_closure_cumulant_data :
    GaugeAnomalyPressureCumulantsFiveData where
  rationalTaylorCoefficients := True
  hasRationalTaylorCoefficients := trivial
  kappa := fold_gauge_anomaly_two_constants_closure_kappa
  kappa_one := by
    simp [fold_gauge_anomaly_two_constants_closure_kappa]
  kappa_two := by
    simp [fold_gauge_anomaly_two_constants_closure_kappa]
  kappa_three := by
    simp [fold_gauge_anomaly_two_constants_closure_kappa]
  kappa_four := by
    simp [fold_gauge_anomaly_two_constants_closure_kappa]
  kappa_five := by
    simp [fold_gauge_anomaly_two_constants_closure_kappa]

/-- The linear coefficient of the odd cubic Taylor truncation for the defect
`Δ(θ) = P_G(θ) - θ - P_G(-θ)`. -/
def fold_gauge_anomaly_two_constants_closure_delta_linear_coeff : ℚ :=
  2 * fold_gauge_anomaly_two_constants_closure_cumulant_data.kappa 1 - 1

/-- The cubic coefficient of the odd cubic Taylor truncation for the defect
`Δ(θ) = P_G(θ) - θ - P_G(-θ)`. -/
def fold_gauge_anomaly_two_constants_closure_delta_cubic_coeff : ℚ :=
  (2 * fold_gauge_anomaly_two_constants_closure_cumulant_data.kappa 3) / 6

/-- The audited odd Taylor truncation through the cubic term. -/
def fold_gauge_anomaly_two_constants_closure_delta_taylor3 (θ : ℚ) : ℚ :=
  fold_gauge_anomaly_two_constants_closure_delta_linear_coeff * θ +
    fold_gauge_anomaly_two_constants_closure_delta_cubic_coeff * θ ^ 3

/-- Concrete closure package combining the audited slope, the golden-ratio far-field value,
the endpoint LDP constants, and the odd cubic Taylor truncation. -/
def FoldGaugeAnomalyTwoConstantsClosure : Prop :=
  Function.Odd gaugeAnomalyGcDefect ∧
    HasDerivAt gaugeAnomalyGcDefect (4 / 9) 0 ∧
    gaugeAnomalyGcFarfieldDefect (Real.log Real.goldenRatio) = Real.log 2 ∧
    gaugeAnomalyEndpointRateZeroClosedForm = Real.log (Nat.fib 7) ∧
    gaugeAnomalyEndpointRateOneClosedForm = Real.log (Nat.fib 8) ∧
    ∀ θ : ℚ,
      fold_gauge_anomaly_two_constants_closure_delta_taylor3 θ =
        (-1 / 9 : ℚ) * θ - (1174 / 6561 : ℚ) * θ ^ 3

/-- Paper label: `cor:fold-gauge-anomaly-two-constants-closure`. -/
theorem paper_fold_gauge_anomaly_two_constants_closure : FoldGaugeAnomalyTwoConstantsClosure := by
  rcases paper_fold_gauge_anomaly_gc_defect_sign with ⟨hOdd, hDeriv, _, _, _⟩
  rcases
      paper_fold_gauge_anomaly_gc_defect_farfield_expansion with ⟨_, _, hFarfieldAtPhi⟩
  rcases
      paper_fold_gauge_anomaly_ldp fold_gauge_anomaly_two_constants_closure_ldp_data with
    ⟨_, hEndpointZero, hEndpointOne⟩
  rcases
      paper_fold_gauge_anomaly_pressure_cumulants_up_to_5
        fold_gauge_anomaly_two_constants_closure_cumulant_data with
    ⟨_, hKappaOne, _, hKappaThree, _, _⟩
  refine ⟨hOdd, hDeriv, hFarfieldAtPhi, ?_, ?_, ?_⟩
  · simpa [GaugeAnomalyLdpData.endpointRateZeroClosed, GaugeAnomalyLdpData.endpointRateZero] using
      hEndpointZero
  · simpa [GaugeAnomalyLdpData.endpointRateOneClosed, GaugeAnomalyLdpData.endpointRateOne] using
      hEndpointOne
  · have hLinear :
        fold_gauge_anomaly_two_constants_closure_delta_linear_coeff = (-1 / 9 : ℚ) := by
      unfold fold_gauge_anomaly_two_constants_closure_delta_linear_coeff
      rw [hKappaOne]
      norm_num
    have hCubic :
        fold_gauge_anomaly_two_constants_closure_delta_cubic_coeff = (-1174 / 6561 : ℚ) := by
      unfold fold_gauge_anomaly_two_constants_closure_delta_cubic_coeff
      rw [hKappaThree]
      norm_num
    intro θ
    rw [fold_gauge_anomaly_two_constants_closure_delta_taylor3, hLinear, hCubic]
    ring

end Omega.Folding
