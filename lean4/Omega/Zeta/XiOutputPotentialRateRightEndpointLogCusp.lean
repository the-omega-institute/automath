import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete endpoint data for the right-endpoint logarithmic cusp of the output-potential
Legendre rate function. The microcanonical branch is recorded separately from the normalized rate
so the theorem below performs the endpoint substitution `I = P(0) - s`. -/
structure xi_output_potential_rate_right_endpoint_log_cusp_data where
  P0 : ℝ
  c : ℝ
  d : ℝ
  A : ℝ
  rateRightEndpoint : ℝ
  microcanonical : ℝ → ℝ
  rate : ℝ → ℝ
  endpointSlope : ℝ → ℝ
  cuspRemainder : ℝ → ℝ
  slopeRemainder : ℝ → ℝ
  A_pos : 0 < A
  A_eq : A = d / (2 * c)
  legendreRelation : ∀ α : ℝ, rate α = P0 - microcanonical α
  endpointMicrocanonical : microcanonical (1 / 2) = P0 - rateRightEndpoint
  microcanonicalLogCusp :
    ∀ ε : ℝ,
      microcanonical (1 / 2 - ε) =
        microcanonical (1 / 2) - 2 * ε * Real.log ε +
          2 * (1 + Real.log A) * ε + ε ^ 2 * cuspRemainder ε
  endpointSlopeExpansion :
    ∀ ε : ℝ,
      endpointSlope (1 / 2 - ε) =
        -2 * Real.log ε + 2 * Real.log A + ε * slopeRemainder ε

namespace xi_output_potential_rate_right_endpoint_log_cusp_data

/-- The normalized rate has the right-endpoint logarithmic cusp and the corresponding endpoint
slope divergence. -/
def rateRightEndpointLogCusp
    (D : xi_output_potential_rate_right_endpoint_log_cusp_data) : Prop :=
  D.A = D.d / (2 * D.c) ∧
    0 < D.A ∧
      D.rate (1 / 2) = D.rateRightEndpoint ∧
        (∀ ε : ℝ,
          D.rate (1 / 2 - ε) =
            D.rateRightEndpoint + 2 * ε * Real.log ε -
              2 * (1 + Real.log D.A) * ε - ε ^ 2 * D.cuspRemainder ε) ∧
          ∀ ε : ℝ,
            D.endpointSlope (1 / 2 - ε) =
              -2 * Real.log ε + 2 * Real.log D.A + ε * D.slopeRemainder ε

end xi_output_potential_rate_right_endpoint_log_cusp_data

/-- Paper label: `thm:xi-output-potential-rate-right-endpoint-log-cusp`. -/
theorem paper_xi_output_potential_rate_right_endpoint_log_cusp
    (D : xi_output_potential_rate_right_endpoint_log_cusp_data) :
    D.rateRightEndpointLogCusp := by
  refine ⟨D.A_eq, D.A_pos, ?_, ?_, D.endpointSlopeExpansion⟩
  · calc
      D.rate (1 / 2) = D.P0 - D.microcanonical (1 / 2) := D.legendreRelation (1 / 2)
      _ = D.rateRightEndpoint := by
        rw [D.endpointMicrocanonical]
        ring
  · intro ε
    calc
      D.rate (1 / 2 - ε) = D.P0 - D.microcanonical (1 / 2 - ε) :=
        D.legendreRelation (1 / 2 - ε)
      _ =
          D.rateRightEndpoint + 2 * ε * Real.log ε -
            2 * (1 + Real.log D.A) * ε - ε ^ 2 * D.cuspRemainder ε := by
        rw [D.microcanonicalLogCusp ε, D.endpointMicrocanonical]
        ring

end Omega.Zeta
