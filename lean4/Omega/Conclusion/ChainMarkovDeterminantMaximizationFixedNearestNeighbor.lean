import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-chain-markov-determinant-maximization-fixed-nearest-neighbor`. -/
theorem paper_conclusion_chain_markov_determinant_maximization_fixed_nearest_neighbor
    (detR detRMC bound loopEntropy : ℝ) (hloop_nonneg : 0 ≤ loopEntropy)
    (hbound : 0 ≤ loopEntropy -> detR ≤ bound) (hmc : detRMC = bound)
    (heq : detR = detRMC ↔ loopEntropy = 0) :
    detR ≤ detRMC ∧ (detR = detRMC ↔ loopEntropy = 0) := by
  constructor
  · rw [hmc]
    exact hbound hloop_nonneg
  · exact heq

end Omega.Conclusion
