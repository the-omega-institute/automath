import Omega.CircleDimension.LocalizedDivisionPrimeFiberNoGrowth
import Omega.CircleDimension.LocalizedGsDualCompleteClassification
import Omega.CircleDimension.SolenoidKernelProductZp

namespace Omega.CircleDimension

open LocalizedDivisionPrimeFiberNoGrowthData
open LocalizedGsEmbeddingOrderData

/-- Rank-one witness for the procyclic-fiber solenoid package. -/
private def procyclicFiberRankOneWitness : LocalizedDivisionPrimeFiberNoGrowthData where
  rank := 1
  dualCarrier := LocalizedDivisionSolenoidModel 1
  kernelCarrier := LocalizedDivisionPrimeFiberModel 1
  dualEquiv := Equiv.refl _
  kernelEquiv := Equiv.refl _
  circleDimension := 1
  kernelCircleDimension := 0
  circleDimension_eq_rank := rfl
  kernelCircleDimension_eq_zero := rfl

/-- Finite prime-support data for the mutual-embedding classification. -/
private def procyclicFiberEmbeddingData
    (S T : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) (hT : ∀ p ∈ T, Nat.Prime p) :
    LocalizedGsEmbeddingOrderData where
  S := S
  T := T
  S_primes := hS
  T_primes := hT

/-- Finite prime support identifies the procyclic fiber with the rank-one localized solenoid,
the projection kernel with the product of `p`-adic coordinates over that support, and the support
itself is unique because mutual localized embeddings force equality of the prime sets.
    cor:cdim-procyclic-fiber-solenoid-classification -/
theorem paper_cdim_procyclic_fiber_solenoid_classification
    (S T : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) (hT : ∀ p ∈ T, Nat.Prime p) :
    (∀ p, p ∈ S → Nat.Prime p) ∧
      Nonempty (LocalizedDivisionSolenoidModel 1 ≃ LocalizedDivisionSolenoidModel 1) ∧
      Nonempty (SolenoidProjectionKernel S ≃ SolenoidKernelProductZpModel S) ∧
      (((localizedEmbedding S T) ∧ (localizedEmbedding T S)) ↔ S = T) := by
  refine ⟨hS, ?_, (paper_cdim_solenoid_kernel_product_zp S).2, ?_⟩
  · have hDual :
        procyclicFiberRankOneWitness.dualIsSolenoid :=
      (paper_cdim_localized_division_prime_fiber_no_growth procyclicFiberRankOneWitness).1
    simpa [LocalizedDivisionPrimeFiberNoGrowthData.dualIsSolenoid, procyclicFiberRankOneWitness]
      using hDual
  · simpa using
      (paper_cdim_localized_gs_dual_complete_classification
        (procyclicFiberEmbeddingData S T hS hT))

end Omega.CircleDimension
