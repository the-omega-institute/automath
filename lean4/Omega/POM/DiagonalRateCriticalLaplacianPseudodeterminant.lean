import Omega.POM.CovarianceLaplacianPdetClosedForm

namespace Omega.POM

open scoped BigOperators

/-- Paper label: `thm:pom-diagonal-rate-critical-laplacian-pseudodeterminant`.
The previously established covariance-Laplacian closed form is exactly the diagonal-rate critical
Laplacian pseudodeterminant formula in the normalized finite setting. -/
theorem paper_pom_diagonal_rate_critical_laplacian_pseudodeterminant
    (k : ℕ) (hk : 2 ≤ k) (q : Fin k → ℚ)
    (hq_pos : ∀ i, 0 < q i) (hq_sum : (∑ i, q i) = 1) :
    covarianceLaplacianPdet q = k * ∏ i, q i := by
  exact paper_covariance_laplacian_pdet_closed_form k hk q hq_pos hq_sum

end Omega.POM
