import Omega.SPG.ScanProjectionBayesOptimality

open Omega.SPG.ScanProjectionBayesOptimality

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Paper-facing seed for the monotonicity corollary in the clarity section:
    one-step refinement cannot increase the prefix scan error, and zero scan
    error is equivalent to exact agreement with some depth-`m` observable event.
    cor:clarity-monotone -/
theorem paper_scan_projection_address_clarity_monotone_seeds
    (μ : PMF (Word n)) (h₀ : m ≤ n) (h₁ : m + 1 ≤ n) (P : Set (Word n)) :
    prefixScanError μ h₁ P ≤ prefixScanError μ h₀ P ∧
      (prefixScanError μ h₀ P = 0 ↔
        ∃ A : Set (Word m), prefixObservableApproxError μ h₀ P A = 0) := by
  refine ⟨prefixScanError_step μ h₀ h₁ P, ?_⟩
  constructor
  · intro hzero
    refine ⟨optimalPrefixDecision μ h₀ P, ?_⟩
    simpa [hzero] using (paper_scan_projection_address_bayes_optimality_seeds μ h₀ P).2
  · rintro ⟨A, hA⟩
    have hle := (paper_scan_projection_address_bayes_optimality_seeds μ h₀ P).1 A
    exact le_antisymm (by simpa [hA] using hle) (zero_le _)

end Omega.SPG
