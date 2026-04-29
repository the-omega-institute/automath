import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.CircleDimension.AFEContractionAttractor

namespace Omega.Conclusion

noncomputable section

/-- The two-scalar posterior real-part error term. -/
def conclusion_xi_posterior_realpart_two_scalar_compression_epsilon
    (eta deltaChi t : ℝ) : ℝ :=
  Real.log ((1 + eta) / (1 - eta)) / Real.log (t / (2 * Real.pi)) +
    |deltaChi| / Real.log (t / (2 * Real.pi))

/-- Paper-facing concrete compression statement obtained from the AFE contraction attractor. -/
def conclusion_xi_posterior_realpart_two_scalar_compression_statement
    (Phi_t : ℝ → ℝ) (sigma eta deltaChi t q : ℝ) : Prop :=
  q < 1 →
    |sigma - Phi_t sigma| ≤
      conclusion_xi_posterior_realpart_two_scalar_compression_epsilon eta deltaChi t →
    Phi_t (1 / 2) = 1 / 2 →
    |Phi_t sigma - Phi_t (1 / 2)| ≤ q * |sigma - 1 / 2| →
    |sigma - 1 / 2| ≤
      conclusion_xi_posterior_realpart_two_scalar_compression_epsilon eta deltaChi t / (1 - q)

/-- Paper label: `thm:conclusion-xi-posterior-realpart-two-scalar-compression`. -/
theorem paper_conclusion_xi_posterior_realpart_two_scalar_compression
    (Phi_t : ℝ → ℝ) (sigma eta deltaChi t q : ℝ) :
    conclusion_xi_posterior_realpart_two_scalar_compression_statement Phi_t sigma eta deltaChi t
      q := by
  intro hq happrox hfixed hcontract
  exact
    Omega.CircleDimension.paper_cdim_afe_contraction_attractor Phi_t sigma
      (conclusion_xi_posterior_realpart_two_scalar_compression_epsilon eta deltaChi t) q hq
      happrox hfixed hcontract

end

end Omega.Conclusion
