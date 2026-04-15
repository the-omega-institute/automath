import Omega.SPG.ClarityMonotone

open Omega.SPG.ScanProjectionBayesOptimality

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for monotonicity and zero-error decidability in the
    prefix-scan paper.
    cor:basic-properties -/
theorem paper_prefix_scan_error_basic_properties
    (μ : PMF (Word n)) (h₁ : m₁ ≤ n) (h₂ : m₂ ≤ n) (hm : m₁ ≤ m₂) (P : Set (Word n)) :
    prefixScanError μ h₂ P ≤ prefixScanError μ h₁ P ∧
      (prefixScanError μ h₁ P = 0 ↔
        ∃ A : Set (Word m₁), prefixObservableApproxError μ h₁ P A = 0) := by
  refine ⟨prefixScanError_antitone μ h₁ h₂ hm P, ?_⟩
  constructor
  · intro hzero
    refine ⟨optimalPrefixDecision μ h₁ P, ?_⟩
    simpa [hzero] using (paper_scan_projection_address_bayes_optimality_package μ h₁ P).2
  · rintro ⟨A, hA⟩
    have hle := (paper_scan_projection_address_bayes_optimality_package μ h₁ P).1 A
    exact le_antisymm (by simpa [hA] using hle) (zero_le _)

end Omega.SPG
