import Mathlib.Tactic
import Omega.CircleDimension.LocalizedDivisionPrimeFiberNoGrowth
import Omega.CircleDimension.LocalizedGsEmbeddingOrder
import Omega.CircleDimension.SolenoidKernelProductZp

namespace Omega.CircleDimension

open LocalizedGsEmbeddingOrderData

/-- Swapping the source and target prime supports in the embedding-order package. -/
private def localizedGsEmbeddingOrderSwap
    (D : LocalizedGsEmbeddingOrderData) : LocalizedGsEmbeddingOrderData where
  S := D.T
  T := D.S
  S_primes := D.T_primes
  T_primes := D.S_primes

/-- A concrete rank-one witness for the localized-division no-growth package. -/
private def localizedGsNoGrowthWitness (_S : Finset ℕ) : LocalizedDivisionPrimeFiberNoGrowthData where
  rank := 1
  dualCarrier := LocalizedDivisionSolenoidModel 1
  kernelCarrier := LocalizedDivisionPrimeFiberModel 1
  dualEquiv := Equiv.refl _
  kernelEquiv := Equiv.refl _
  circleDimension := 1
  kernelCircleDimension := 0
  circleDimension_eq_rank := rfl
  kernelCircleDimension_eq_zero := rfl

/-- Mutual localized embeddings force equality of the finite prime supports, and equality gives
the two embeddings back by the identity scaling.
    cor:cdim-localized-gs-dual-complete-classification -/
theorem paper_cdim_localized_gs_dual_complete_classification
    (D : Omega.CircleDimension.LocalizedGsEmbeddingOrderData) :
    ((Omega.CircleDimension.LocalizedGsEmbeddingOrderData.localizedEmbedding D.S D.T) ∧
      (Omega.CircleDimension.LocalizedGsEmbeddingOrderData.localizedEmbedding D.T D.S)) ↔
      D.S = D.T := by
  constructor
  · rintro ⟨hSTEmb, hTSEmb⟩
    have hST : D.S ⊆ D.T := (paper_cdim_localized_gs_embedding_order D).1.mp hSTEmb
    have hTS : D.T ⊆ D.S :=
      (paper_cdim_localized_gs_embedding_order (localizedGsEmbeddingOrderSwap D)).1.mp hTSEmb
    exact Finset.Subset.antisymm hST hTS
  · intro hST
    have hSelf : localizedEmbedding D.S D.S := localizedEmbedding_of_subset (by intro p hp; exact hp)
    constructor <;> simpa [hST] using hSelf

/-- The no-growth package gives the rank-one circle-dimension and zero kernel-dimension
consequences used in the paper discussion of the localized dual classification. -/
theorem localizedGs_circleDimension_and_kernelDimension (S : Finset ℕ) :
    (localizedGsNoGrowthWitness S).circleDimension = 1 ∧
      (localizedGsNoGrowthWitness S).kernelCircleDimension = 0 := by
  rcases paper_cdim_localized_division_prime_fiber_no_growth (localizedGsNoGrowthWitness S) with
    ⟨_, _, hCircle, hKernel⟩
  exact ⟨hCircle, hKernel⟩

/-- The kernel of the localized solenoid projection is the explicit product of the `p`-adic
integers over the finite prime support. -/
theorem localizedGs_kernel_product_zp (S : Finset ℕ) :
    Nonempty (SolenoidProjectionKernel S ≃ SolenoidKernelProductZpModel S) := by
  exact (paper_cdim_solenoid_kernel_product_zp S).2

end Omega.CircleDimension
