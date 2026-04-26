import Omega.Core.WalshStokes

namespace Omega.Discussion

/-- Paper-facing discussion wrapper for the Walsh bias bound by boundary variation.
    cor:discussion-walsh-bias-controlled-by-boundary-variation -/
theorem paper_discussion_walsh_bias_controlled_by_boundary_variation
    (n : Nat) (A : Finset (Fin n)) (f : Omega.Word n → ℤ) :
    Int.natAbs (Omega.Core.walshFlux A f) ≤
      ∑ w : Omega.Core.BoundaryWords A, Int.natAbs (Omega.Core.deltaSet A f w.1) := by
  simpa using Omega.Core.walshBias_le_boundaryVariation (n := n) A f

end Omega.Discussion
