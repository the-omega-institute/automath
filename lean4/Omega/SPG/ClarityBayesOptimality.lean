import Omega.SPG.ScanProjectionBayesOptimality

namespace Omega.SPG

/-- Paper-facing wrapper for the prefix Bayes-optimal scan-clarity decision rule.
    prop:spg-clarity-bayes-optimality -/
theorem paper_spg_clarity_bayes_optimality {n m : Nat} (μ : PMF (Word n)) (h : m ≤ n)
    (P : Set (Word n)) :
    (∀ A : Set (Word m), prefixScanError μ h P ≤
      ScanProjectionBayesOptimality.prefixObservableApproxError μ h P A) ∧
      ScanProjectionBayesOptimality.prefixObservableApproxError μ h P
        (ScanProjectionBayesOptimality.optimalPrefixDecision μ h P) =
        prefixScanError μ h P := by
  simpa using
    Omega.SPG.ScanProjectionBayesOptimality.paper_scan_projection_address_bayes_optimality_package
      μ h P

end Omega.SPG
