import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-poisson-cauchy-chi2-dissipation-identity`. -/
theorem paper_xi_poisson_cauchy_chi2_dissipation_identity
    (chi2Derivative dissipation : ℝ)
    (hDerivative : chi2Derivative = -2 * dissipation)
    (hDissipation_nonneg : 0 ≤ dissipation) :
    chi2Derivative = -2 * dissipation ∧ chi2Derivative ≤ 0 := by
  constructor
  · exact hDerivative
  · nlinarith

end Omega.Zeta
