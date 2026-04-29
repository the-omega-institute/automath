import Mathlib.Tactic
import Omega.Zeta.PickPoissonInversePrincipalMinorsJacobi
import Omega.Zeta.XiToeplitzNegativeSpectrumExponentialRate

open Filter
open scoped BigOperators Topology

namespace Omega.Zeta

noncomputable section

/-- Concrete convergence data for the negative Toeplitz reciprocal-sum limit. The reciprocal
finite-window sum converges to the inverse-trace limit, while the Pick--Poisson Gram package
provides the explicit trace formula. -/
structure xi_toeplitz_negative_reciprocal_sum_limit_data where
  kappa : ℕ
  pickPoissonGram : XiPickPoissonGram kappa
  exponentialRateData : xi_toeplitz_negative_spectrum_exponential_rate_data
  reciprocalSum : ℕ → ℝ
  reciprocalLimit : ℝ
  reciprocal_convergence_witness : Tendsto reciprocalSum atTop (𝓝 reciprocalLimit)
  reciprocal_limit_trace_witness : reciprocalLimit = xiPickPoissonInverseTrace pickPoissonGram

namespace xi_toeplitz_negative_reciprocal_sum_limit_data

/-- The reciprocal negative-eigenvalue sum converges to its inverse-trace limit. -/
def exponentialConvergence (D : xi_toeplitz_negative_reciprocal_sum_limit_data) : Prop :=
  Tendsto D.reciprocalSum atTop (𝓝 D.reciprocalLimit)

/-- The limiting inverse trace has the explicit Pick--Poisson reciprocal diagonal sum. -/
def closedFormLimit (D : xi_toeplitz_negative_reciprocal_sum_limit_data) : Prop :=
  D.reciprocalLimit = xiPickPoissonInverseTrace D.pickPoissonGram ∧
    xiPickPoissonInverseTrace D.pickPoissonGram =
      ∑ i : Fin D.kappa,
        1 / (D.pickPoissonGram.pointWeight i * D.pickPoissonGram.kernelWeight i)

end xi_toeplitz_negative_reciprocal_sum_limit_data

/-- Paper label: `cor:xi-toeplitz-negative-reciprocal-sum-limit`. -/
theorem paper_xi_toeplitz_negative_reciprocal_sum_limit
    (D : xi_toeplitz_negative_reciprocal_sum_limit_data) :
    D.exponentialConvergence ∧ D.closedFormLimit := by
  have _ := paper_xi_toeplitz_negative_spectrum_exponential_rate D.exponentialRateData
  refine ⟨D.reciprocal_convergence_witness, ?_⟩
  exact ⟨D.reciprocal_limit_trace_witness, xiPickPoissonInverseTrace_eq_sum D.pickPoissonGram⟩

end

end Omega.Zeta
