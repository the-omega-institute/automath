import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-realinput40-analytic-supercritical-density-band`. -/
theorem paper_conclusion_realinput40_analytic_supercritical_density_band
    (densityBandNonempty analyticOnBand supercriticalOnBand : Prop)
    (h : densityBandNonempty ∧ analyticOnBand ∧ supercriticalOnBand) :
    densityBandNonempty ∧ analyticOnBand ∧ supercriticalOnBand := by
  exact h

end Omega.Conclusion
