import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-cross-energy-gaussian-mutual-information`. -/
theorem paper_xi_cross_energy_gaussian_mutual_information
    (crossEnergy mutualInfo logDetA logDetB logDetAB : ℝ)
    (hcross : crossEnergy = -logDetAB + logDetA + logDetB)
    (hmi : mutualInfo = logDetA + logDetB - logDetAB) :
    crossEnergy = mutualInfo := by
  rw [hcross, hmi]
  ring

end Omega.Zeta
