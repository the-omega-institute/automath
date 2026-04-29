import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Paper label: `prop:xi-cross-energy-gaussian-mutual-information`. Abstract entropy
bookkeeping for the Gaussian mutual-information identity: once the cross-energy and
entropy terms are unfolded as logarithmic determinants, both sides are the same
linear combination of log-determinants. -/
theorem paper_xi_cross_energy_gaussian_mutual_information
    (crossEnergy mutualInformation detUnion detA detB entropyUnion entropyA entropyB : ℝ)
    (hcross : crossEnergy = -Real.log detUnion + Real.log detA + Real.log detB)
    (hentropyUnion : entropyUnion = Real.log detUnion)
    (hentropyA : entropyA = Real.log detA)
    (hentropyB : entropyB = Real.log detB)
    (hmi : mutualInformation = entropyA + entropyB - entropyUnion) :
    crossEnergy = mutualInformation := by
  rw [hcross, hmi, hentropyUnion, hentropyA, hentropyB]
  ring

end
end Omega.Zeta
