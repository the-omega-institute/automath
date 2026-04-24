import Omega.CircleDimension.FinitePrimeTruncationKernels
import Omega.CircleDimension.LocalizedGsEmbeddingOrder

namespace Omega.CircleDimension

open LocalizedGsEmbeddingOrderData

/-- Over the common torus factor, a morphism `K_S → K_T` exists exactly when the discrete
localization inclusion goes the opposite way, and in that case the resulting finite-prime
truncation map is surjective with kernel the product of the newly added `p`-adic axes.
    thm:cdim-solenoid-over-t-morphism-classification -/
theorem paper_cdim_solenoid_over_t_morphism_classification (D : LocalizedGsEmbeddingOrderData) :
    (LocalizedGsEmbeddingOrderData.compatibleDualSurjection D.S D.T ↔ D.S ⊆ D.T) ∧
      ∀ hST : D.S ⊆ D.T,
        Function.Surjective (finitePrimeTruncationMap hST) ∧
          Nonempty (FinitePrimeTruncationKernel hST ≃ AddedPrimeProduct D.S D.T) := by
  refine ⟨?_, ?_⟩
  · simpa [LocalizedGsEmbeddingOrderData.compatibleDualSurjection] using
      (paper_cdim_localized_gs_embedding_order D).2
  · intro hST
    exact
      ⟨finitePrimeTruncationMap_surjective hST,
        ⟨finitePrimeTruncationKernelEquivAddedPrimeProduct hST⟩⟩

end Omega.CircleDimension
