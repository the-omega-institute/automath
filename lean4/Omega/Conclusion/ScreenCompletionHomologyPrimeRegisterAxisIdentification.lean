import Mathlib.Tactic
import Omega.Conclusion.FixedResolutionScreenCorankAuditCostLaw

namespace Omega.Conclusion

open Finset

/-- Concrete fixed-resolution package for the identification of completion count, corank,
kernel rank, homology rank, and the doubled prime-register axis count. -/
structure ConclusionScreenCompletionHomologyPrimeRegisterAxisIdentificationData where
  Vertex : Type
  decEqVertex : DecidableEq Vertex
  m : ℕ
  n : ℕ
  ρ : ℕ
  rank : Finset Vertex → ℕ
  hm : 1 ≤ m
  hn : 1 ≤ n
  rank_bounded : ∀ s, rank s ≤ ρ
  rank_submod : ∀ s t, rank (s ∩ t) + rank (s ∪ t) ≤ rank s + rank t

attribute [instance]
  ConclusionScreenCompletionHomologyPrimeRegisterAxisIdentificationData.decEqVertex

/-- Visible completion count at fixed resolution. -/
def ConclusionScreenCompletionHomologyPrimeRegisterAxisIdentificationData.completionCount
    (D : ConclusionScreenCompletionHomologyPrimeRegisterAxisIdentificationData) : ℕ :=
  fixedResolutionScreenAuditCost D.m D.n

/-- Corank bookkeeping for the same fixed-resolution screen. -/
def ConclusionScreenCompletionHomologyPrimeRegisterAxisIdentificationData.corank
    (D : ConclusionScreenCompletionHomologyPrimeRegisterAxisIdentificationData) : ℕ :=
  fixedResolutionScreenAuditCost D.m D.n

/-- Kernel-rank term provided by the existing fixed-resolution corank/audit package. -/
def ConclusionScreenCompletionHomologyPrimeRegisterAxisIdentificationData.kernelRank
    (D : ConclusionScreenCompletionHomologyPrimeRegisterAxisIdentificationData) : ℕ :=
  fixedResolutionScreenKernelRank D.m D.n

/-- Relative-homology rank attached to the same screen. -/
def ConclusionScreenCompletionHomologyPrimeRegisterAxisIdentificationData.homologyRank
    (D : ConclusionScreenCompletionHomologyPrimeRegisterAxisIdentificationData) : ℕ :=
  fixedResolutionScreenHomologyRank D.m D.n

/-- Positive/negative prime-register splitting doubles the kernel-rank axis count. -/
def ConclusionScreenCompletionHomologyPrimeRegisterAxisIdentificationData.primeRegisterAxes
    (D : ConclusionScreenCompletionHomologyPrimeRegisterAxisIdentificationData) : ℕ :=
  2 * D.kernelRank

/-- Paper label:
`thm:conclusion-screen-completion-homology-prime-register-axis-identification`. -/
theorem paper_conclusion_screen_completion_homology_prime_register_axis_identification
    (D : ConclusionScreenCompletionHomologyPrimeRegisterAxisIdentificationData) :
    D.completionCount = D.corank ∧
      D.corank = D.kernelRank ∧
      D.kernelRank = D.homologyRank ∧
      D.primeRegisterAxes = 2 * D.completionCount := by
  rcases
      paper_conclusion_fixedresolution_screen_corank_audit_cost_law
        (V := D.Vertex) D.m D.n D.ρ D.rank D.hm D.hn D.rank_bounded D.rank_submod
    with ⟨haudit_kernel, hkernel_homology, _, _, _, _⟩
  refine ⟨rfl, ?_, hkernel_homology, ?_⟩
  · simpa [
      ConclusionScreenCompletionHomologyPrimeRegisterAxisIdentificationData.corank,
      ConclusionScreenCompletionHomologyPrimeRegisterAxisIdentificationData.kernelRank
    ] using haudit_kernel
  · calc
      D.primeRegisterAxes = 2 * D.kernelRank := by rfl
      _ = 2 * fixedResolutionScreenAuditCost D.m D.n := by
        exact congrArg (fun t => 2 * t) haudit_kernel.symm
      _ = 2 * D.completionCount := by rfl

end Omega.Conclusion
