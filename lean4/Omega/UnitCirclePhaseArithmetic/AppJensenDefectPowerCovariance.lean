import Omega.TypedAddressBiaxialCompletion.JensenDefectPowerCovariance

namespace Omega.UnitCirclePhaseArithmetic

/-- The Jensen defect attached to an energy/entropy pair. -/
def appJensenDefect (energy entropy : ℝ) : ℝ :=
  energy - entropy

/-- Power pullback leaves the Jensen defect unchanged after the deterministic radius
reparameterization.
    prop:app-jensen-defect-power-covariance -/
theorem paper_app_jensen_defect_power_covariance
    (m : ℕ) (hm : 1 ≤ m) (energyF energyG entropyF entropyG : ℝ)
    (hEnergy : energyG = energyF) (hEntropy : entropyG = entropyF) :
    appJensenDefect energyG entropyG = appJensenDefect energyF entropyF := by
  have htyped :=
    Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_jensen_defect_power_covariance
      m energyF energyG entropyF entropyG (appJensenDefect energyF entropyF)
      (appJensenDefect energyG entropyG) hm hEnergy hEntropy rfl rfl
  simpa [appJensenDefect] using htyped

end Omega.UnitCirclePhaseArithmetic
