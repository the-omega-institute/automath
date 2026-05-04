import Omega.CircleDimension.ProcyclicFiberSolenoidClassification
import Omega.CircleDimension.SolenoidRigidityRankPrimeSupport
import Omega.Zeta.XiTimePart9zlLocalizedSolenoidPrimeOrthogonality

namespace Omega.Zeta

/-- Finite prime-support localized solenoids have rank-one circle dimension data, their
projection kernel is the product of the retained prime coordinates, mutual localized embeddings
recover the finite support, and any solenoid isomorphism transports both rank and prime support. -/
def xi_time_part9zl_localization_circle_collapse_support_rigidity_statement : Prop :=
  (∀ S T : Finset ℕ, (∀ p ∈ S, Nat.Prime p) → (∀ p ∈ T, Nat.Prime p) →
      (∀ p, p ∈ S → Nat.Prime p) ∧
        (∀ p, p ∈ T → Nat.Prime p) ∧
        Nonempty
          (Omega.CircleDimension.LocalizedDivisionSolenoidModel 1 ≃
            Omega.CircleDimension.LocalizedDivisionSolenoidModel 1) ∧
        Nonempty
          (Omega.CircleDimension.SolenoidProjectionKernel S ≃
            Omega.CircleDimension.SolenoidKernelProductZpModel S) ∧
        (((Omega.CircleDimension.LocalizedGsEmbeddingOrderData.localizedEmbedding S T) ∧
            (Omega.CircleDimension.LocalizedGsEmbeddingOrderData.localizedEmbedding T S)) ↔
          S = T)) ∧
    (∀ S T : Finset ℕ,
      xi_time_part9zl_localized_solenoid_prime_orthogonality_statement S T) ∧
    (∀ D : Omega.CircleDimension.SolenoidRigidityRankPrimeSupportData,
      D.sourceRank = D.targetRank ∧ D.sourcePrimeSupport = D.targetPrimeSupport)

/-- Paper label:
`cor:xi-time-part9zl-localization-circle-collapse-support-rigidity`. -/
theorem paper_xi_time_part9zl_localization_circle_collapse_support_rigidity :
    xi_time_part9zl_localization_circle_collapse_support_rigidity_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro S T hS hT
    rcases Omega.CircleDimension.paper_cdim_procyclic_fiber_solenoid_classification S T hS hT with
      ⟨hS', hDual, hKernel, hRigidity⟩
    exact ⟨hS', hT, hDual, hKernel, hRigidity⟩
  · intro S T
    exact paper_xi_time_part9zl_localized_solenoid_prime_orthogonality S T
  · intro D
    exact Omega.CircleDimension.paper_cdim_solenoid_rigidity_rank_prime_support D

end Omega.Zeta
