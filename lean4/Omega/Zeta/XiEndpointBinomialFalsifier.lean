import Omega.Zeta.XiBinomialToeplitzDominantPoleResponse

namespace Omega.Zeta

/-- Paper label: `thm:xi-endpoint-binomial-falsifier`. -/
theorem paper_xi_endpoint_binomial_falsifier
    (D : XiBinomialToeplitzDominantPoleResponseData)
    (hneg : (Nat.choose (2 * D.N) D.N : ℝ) * D.dominantPole +
      D.holomorphicRemainder < 0) :
    D.endpointQuadraticResponse < 0 := by
  have hclosed := (paper_xi_binomial_toeplitz_dominant_pole_response D).1
  unfold XiBinomialToeplitzDominantPoleResponseData.closedFormResponseLaw at hclosed
  rw [hclosed]
  exact hneg

end Omega.Zeta
