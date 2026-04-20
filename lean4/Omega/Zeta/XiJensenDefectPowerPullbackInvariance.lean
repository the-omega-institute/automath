import Mathlib.Tactic

namespace Omega.Zeta

/-- `prop:xi-jensen-defect-power-pullback-invariance` -/
theorem paper_xi_jensen_defect_power_pullback_invariance (m : ℕ)
    (energyF energyG entropyF entropyG defectF defectG : ℝ) (hm : 1 ≤ m)
    (hEnergy : energyG = energyF) (hEntropy : entropyG = entropyF)
    (hDefectF : defectF = energyF - entropyF) (hDefectG : defectG = energyG - entropyG) :
    defectG = defectF := by
  let _ := hm
  calc
    defectG = energyG - entropyG := hDefectG
    _ = energyF - entropyF := by rw [hEnergy, hEntropy]
    _ = defectF := by rw [← hDefectF]

end Omega.Zeta
