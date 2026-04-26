import Omega.CircleDimension.MedianMinPrimeSpectrumCubeDimension
import Omega.CircleDimension.MedianThetaRigidityPrimeRatio

namespace Omega.Conclusion

open Omega.CircleDimension

/-- Packaging of the prime-support minimal-rigidity conclusion from the two `CircleDimension`
ingredients: the normalized `Θ`-labeling is unique, and every embedding uses at least one visible
prime per `Θ`-class.
    thm:conclusion-median-prime-support-minimal-rigidity -/
theorem paper_conclusion_median_prime_support_minimal_rigidity
    (P : PrimeRatioEmbeddingPackage) [Fintype P.ThetaClass] :
    (∀ ι : P.ThetaClass → ℕ, InducesThetaLabel P ι → ι = P.thetaPrime) ∧
      ∃ primesUsed : Finset ℕ,
        (∀ H, P.thetaPrime H ∈ primesUsed) ∧ Fintype.card P.ThetaClass ≤ primesUsed.card := by
  rcases paper_cdim_median_theta_rigidity_prime_ratio P with ⟨_, _, _, _, huniq⟩
  exact ⟨huniq, paper_cdim_median_min_prime_spectrum_cube_dimension P⟩

end Omega.Conclusion
