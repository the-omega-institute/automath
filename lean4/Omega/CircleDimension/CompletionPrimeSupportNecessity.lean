import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Concrete audit-completion record used to track the free ledger rank together with the visible
prime support carried by the completion. -/
structure AuditCompletion where
  freeRank : ℕ
  primeSupport : Finset ℕ

/-- Minimal concrete data for the prime-support necessity statement: the kernel contributes a fixed
prime support, and every admissible completion must keep at least the audited free rank. -/
structure CompletionPrimeSupportData where
  kernelPrimeSupport : Finset ℕ
  minimalFreeRank : ℕ

namespace CompletionPrimeSupportData

/-- An audit completion must contain the kernel prime support and carry at least the minimal free
rank required by the audit. -/
def IsAuditCompletion (D : CompletionPrimeSupportData) (R : AuditCompletion) : Prop :=
  D.kernelPrimeSupport ⊆ R.primeSupport ∧ D.minimalFreeRank ≤ R.freeRank

/-- Minimality is measured only in free-rank cost, since the circle-dimension bookkeeping is
torsion-insensitive in this toy model. -/
def IsMinimalAuditCompletion (D : CompletionPrimeSupportData) (R : AuditCompletion) : Prop :=
  D.IsAuditCompletion R ∧ ∀ S, D.IsAuditCompletion S → R.freeRank ≤ S.freeRank

/-- Restricting the optimal completion to the audited kernel support yields the exact prime-support
realization without increasing the free-rank cost. -/
def optimalCompletion (D : CompletionPrimeSupportData) : AuditCompletion where
  freeRank := D.minimalFreeRank
  primeSupport := D.kernelPrimeSupport

lemma optimalCompletion_isAuditCompletion (D : CompletionPrimeSupportData) :
    D.IsAuditCompletion D.optimalCompletion := by
  constructor
  · intro p hp
    exact hp
  · exact le_rfl

lemma optimalCompletion_isMinimal (D : CompletionPrimeSupportData) :
    D.IsMinimalAuditCompletion D.optimalCompletion := by
  refine ⟨D.optimalCompletion_isAuditCompletion, ?_⟩
  intro S hS
  exact hS.2

end CompletionPrimeSupportData

open CompletionPrimeSupportData

/-- Any audit completion must contain the kernel prime support, and the optimal completion can be
restricted to that support without increasing the free-rank cost.
    prop:cdim-completion-prime-support-necessity -/
theorem paper_cdim_completion_prime_support_necessity (D : CompletionPrimeSupportData) :
    (∀ R, D.IsAuditCompletion R → D.kernelPrimeSupport ⊆ R.primeSupport) ∧
      ∃ R, D.IsMinimalAuditCompletion R ∧ R.primeSupport = D.kernelPrimeSupport := by
  refine ⟨?_, ?_⟩
  · intro R hR
    exact hR.1
  · refine ⟨D.optimalCompletion, D.optimalCompletion_isMinimal, rfl⟩

end Omega.CircleDimension
