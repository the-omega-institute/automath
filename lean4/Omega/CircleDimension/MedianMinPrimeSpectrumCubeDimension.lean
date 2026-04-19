import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Omega.CircleDimension.MedianThetaRigidityPrimeRatio

namespace Omega.CircleDimension

/-- The prime labels used by an addressable median prime-ratio embedding contain the full image of
`thetaPrime`, hence at least one prime for each `Θ`-class.
    cor:cdim-median-min-prime-spectrum-cube-dimension -/
theorem paper_cdim_median_min_prime_spectrum_cube_dimension (P : PrimeRatioEmbeddingPackage)
    [Fintype P.ThetaClass] :
    ∃ primesUsed : Finset ℕ,
      (∀ H, P.thetaPrime H ∈ primesUsed) ∧ Fintype.card P.ThetaClass ≤ primesUsed.card := by
  classical
  refine ⟨Finset.univ.image P.thetaPrime, ?_, ?_⟩
  · intro H
    exact Finset.mem_image.mpr ⟨H, Finset.mem_univ H, rfl⟩
  · have hcard :
        (Finset.univ.image P.thetaPrime).card = Fintype.card P.ThetaClass := by
      simpa using Finset.card_image_of_injective (s := Finset.univ) P.thetaPrime_injective
    exact hcard.symm.le

end Omega.CircleDimension
