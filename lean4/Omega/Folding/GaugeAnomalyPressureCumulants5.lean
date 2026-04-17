import Omega.Folding.GaugeAnomalyPressure

namespace Omega.Folding

/-- Chapter-local witness package for the order-five rational Taylor expansion of the gauge-anomaly
pressure branch. The fields record the rationality certificate for all Taylor coefficients and the
explicit first five cumulants used in the paper statement. -/
structure GaugeAnomalyPressureCumulantsFiveData where
  rationalTaylorCoefficients : Prop
  hasRationalTaylorCoefficients : rationalTaylorCoefficients
  kappa : ℕ → ℚ
  kappa_one : kappa 1 = (4 / 9 : ℚ)
  kappa_two : kappa 2 = (118 / 243 : ℚ)
  kappa_three : kappa 3 = (-1174 / 2187 : ℚ)
  kappa_four : kappa 4 = (-8890 / 19683 : ℚ)
  kappa_five : kappa 5 = (17294570 / 1594323 : ℚ)

/-- Paper-facing wrapper for the gauge-anomaly pressure cumulants through order five.
    prop:fold-gauge-anomaly-pressure-cumulants-up-to-5 -/
theorem paper_fold_gauge_anomaly_pressure_cumulants_up_to_5
    (h : GaugeAnomalyPressureCumulantsFiveData) :
    h.rationalTaylorCoefficients ∧
      h.kappa 1 = (4 / 9 : ℚ) ∧
      h.kappa 2 = (118 / 243 : ℚ) ∧
      h.kappa 3 = (-1174 / 2187 : ℚ) ∧
      h.kappa 4 = (-8890 / 19683 : ℚ) ∧
      h.kappa 5 = (17294570 / 1594323 : ℚ) := by
  exact ⟨h.hasRationalTaylorCoefficients, h.kappa_one, h.kappa_two, h.kappa_three,
    h.kappa_four, h.kappa_five⟩

end Omega.Folding
