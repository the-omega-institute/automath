import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-toeplitz-length-vs-boundary-depth`. -/
theorem paper_xi_toeplitz_length_vs_boundary_depth
    (toeplitzThreshold depthDivergence coarseLowerBound : Prop)
    (hThreshold : toeplitzThreshold) (hDepth : toeplitzThreshold -> depthDivergence)
    (hCoarse : depthDivergence -> coarseLowerBound) :
    toeplitzThreshold ∧ depthDivergence ∧ coarseLowerBound := by
  have hDivergence : depthDivergence := hDepth hThreshold
  exact ⟨hThreshold, hDivergence, hCoarse hDivergence⟩

end Omega.Zeta
