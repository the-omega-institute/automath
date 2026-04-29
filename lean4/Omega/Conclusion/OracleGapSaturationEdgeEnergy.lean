import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-oracle-gap-saturation-edge-energy`. -/
theorem paper_conclusion_oracle_gap_saturation_edge_energy
    (logTwo muPhi gapArea edgeEnergy : ℝ)
    (henergy : edgeEnergy = logTwo * muPhi - 2 * gapArea) :
    (1 / 2 : ℝ) * logTwo * muPhi - gapArea = (1 / 2 : ℝ) * edgeEnergy := by
  rw [henergy]
  ring

end Omega.Conclusion
