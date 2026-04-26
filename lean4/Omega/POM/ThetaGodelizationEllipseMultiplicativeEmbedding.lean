import Omega.POM.ThetaGodelizationPrimeValuationIsometry

namespace Omega.POM

/-- Paper label: `cor:pom-theta-godelization-ellipse-multiplicative-embedding`. -/
theorem paper_pom_theta_godelization_ellipse_multiplicative_embedding
    (primeValuationEmbedding ellipseParameterInjective edgePrimeUpdate ellipseEmbeddingInjective :
      Prop)
    (hPrime : primeValuationEmbedding)
    (hEllipse : primeValuationEmbedding -> ellipseParameterInjective -> ellipseEmbeddingInjective)
    (hUpdate : primeValuationEmbedding -> edgePrimeUpdate)
    (hParam : ellipseParameterInjective) :
    ellipseEmbeddingInjective ∧ edgePrimeUpdate := by
  have hPackage :
      primeValuationEmbedding ∧ primeValuationEmbedding ∧ edgePrimeUpdate :=
    paper_pom_theta_godelization_prime_valuation_isometry
      primeValuationEmbedding primeValuationEmbedding edgePrimeUpdate hPrime (fun h => h) hUpdate
  exact ⟨hEllipse hPackage.2.1 hParam, hPackage.2.2⟩

end Omega.POM
