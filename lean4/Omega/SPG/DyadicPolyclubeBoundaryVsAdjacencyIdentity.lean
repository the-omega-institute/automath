import Std

namespace Omega.SPG

/-- Boundary-face count equals total cube faces minus twice the internal shared-face count.
    prop:spg-dyadic-polyclube-boundary-vs-adjacency-identity -/
theorem paper_spg_dyadic_polyclube_boundary_vs_adjacency_identity
    (externalFaces internalPairs cubeCount dim : Nat)
    (hdecomp : 2 * dim * cubeCount = externalFaces + 2 * internalPairs) :
    externalFaces = 2 * dim * cubeCount - 2 * internalPairs := by
  have h' : externalFaces + 2 * internalPairs = 2 * dim * cubeCount := by
    simpa using hdecomp.symm
  exact Nat.eq_sub_of_add_eq h'

end Omega.SPG
