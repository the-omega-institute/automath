namespace Omega.POM

/-- Paper-facing wrapper for the partial-cube coordinate, valuation-embedding, and arithmetic
    distance identifications.
    thm:pom-theta-godelization-prime-valuation-isometry -/
theorem paper_pom_theta_godelization_prime_valuation_isometry
    (thetaCoordinateIsometry primeValuationEmbedding arithmeticDistanceEquality : Prop)
    (h_coord : thetaCoordinateIsometry)
    (h_embed : thetaCoordinateIsometry -> primeValuationEmbedding)
    (h_dist : primeValuationEmbedding -> arithmeticDistanceEquality) :
    thetaCoordinateIsometry ∧ primeValuationEmbedding ∧ arithmeticDistanceEquality := by
  have hembed : primeValuationEmbedding := h_embed h_coord
  exact ⟨h_coord, hembed, h_dist hembed⟩

end Omega.POM
