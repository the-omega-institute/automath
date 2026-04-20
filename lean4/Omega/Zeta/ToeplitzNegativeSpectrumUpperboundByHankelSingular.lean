import Mathlib.Tactic
import Omega.Zeta.ToeplitzNegativeSubspacePreservationThreshold

namespace Omega.Zeta

/-- Paper-facing upper bound for the negative Toeplitz directions coming from the Hankel singular
lower bound: each distinguished Rayleigh direction is bounded by the explicit shifted quantity
`‖R_N‖² ‖E_N‖ - σ_j²`, hence is strictly negative below the perturbative threshold.
    thm:xi-toeplitz-negative-spectrum-upperbound-by-hankel-singular -/
theorem paper_xi_toeplitz_negative_spectrum_upperbound_by_hankel_singular
    (D : ToeplitzNegativeSubspacePreservationThresholdData) :
    D.opNormEN < D.sigmaMinH ^ 2 / D.opNormR ^ 2 →
      ∀ i, D.witnessQuadraticForm i ≤ D.opNormR ^ 2 * D.opNormEN - D.sigmaMinH ^ 2 ∧
        D.witnessQuadraticForm i < 0 := by
  intro hThreshold i
  refine ⟨D.witnessBound i, ?_⟩
  exact paper_xi_toeplitz_negative_subspace_preservation_threshold D hThreshold i

end Omega.Zeta
