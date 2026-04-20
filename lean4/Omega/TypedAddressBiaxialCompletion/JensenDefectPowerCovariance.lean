import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- Power pullback preserves the Jensen-defect energy/entropy decomposition, so the defect itself
is unchanged after transporting along the `m`-fold cover.
    prop:typed-address-biaxial-completion-jensen-defect-power-covariance -/
theorem paper_typed_address_biaxial_completion_jensen_defect_power_covariance
    (m : Nat) (energyF energyG entropyF entropyG defectF defectG : Real) (hm : 1 <= m)
    (hEnergy : energyG = energyF) (hEntropy : entropyG = entropyF)
    (hDefectF : defectF = energyF - entropyF) (hDefectG : defectG = energyG - entropyG) :
    defectG = defectF := by
  let _ := hm
  calc
    defectG = energyG - entropyG := hDefectG
    _ = energyF - entropyF := by rw [hEnergy, hEntropy]
    _ = defectF := hDefectF.symm

end Omega.TypedAddressBiaxialCompletion
