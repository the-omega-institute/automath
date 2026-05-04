import Mathlib.Tactic

namespace Omega.Conclusion

/-- The endpoint moment bound and spectral-margin lower bound combine into exponential
collapse of the Toeplitz minimum, with the central-binomial comparison kept separate. -/
def conclusion_endpoint_gap_forces_exponential_collapse_of_toeplitz_minimum_statement
    (N : ℕ) (toeplitzMinimum massOnGap gapRatio centralRatio asymptoticEnvelope : ℝ) :
    Prop :=
  toeplitzMinimum ≤ (massOnGap * gapRatio ^ (2 * N)) * centralRatio ∧
    toeplitzMinimum ≤ (massOnGap * gapRatio ^ (2 * N)) * asymptoticEnvelope ∧
    centralRatio ≤ asymptoticEnvelope

/-- Paper label:
`thm:conclusion-endpoint-gap-forces-exponential-collapse-of-toeplitz-minimum`. -/
theorem paper_conclusion_endpoint_gap_forces_exponential_collapse_of_toeplitz_minimum
    {N : ℕ} {toeplitzMinimum endpointMoment massOnGap gapRatio centralRatio
      asymptoticEnvelope : ℝ}
    (h_endpoint_moment_bound : endpointMoment ≤ massOnGap * gapRatio ^ (2 * N))
    (h_toeplitz_spectral_margin : toeplitzMinimum ≤ endpointMoment * centralRatio)
    (h_centralRatio_nonneg : 0 ≤ centralRatio)
    (h_gap_envelope_nonneg : 0 ≤ massOnGap * gapRatio ^ (2 * N))
    (h_central_binomial_asymptotic_certificate : centralRatio ≤ asymptoticEnvelope) :
    conclusion_endpoint_gap_forces_exponential_collapse_of_toeplitz_minimum_statement N
      toeplitzMinimum massOnGap gapRatio centralRatio asymptoticEnvelope := by
  have h_first :
      toeplitzMinimum ≤ (massOnGap * gapRatio ^ (2 * N)) * centralRatio := by
    calc
      toeplitzMinimum ≤ endpointMoment * centralRatio := h_toeplitz_spectral_margin
      _ ≤ (massOnGap * gapRatio ^ (2 * N)) * centralRatio :=
        mul_le_mul_of_nonneg_right h_endpoint_moment_bound h_centralRatio_nonneg
  have h_second :
      toeplitzMinimum ≤ (massOnGap * gapRatio ^ (2 * N)) * asymptoticEnvelope := by
    calc
      toeplitzMinimum ≤ (massOnGap * gapRatio ^ (2 * N)) * centralRatio := h_first
      _ ≤ (massOnGap * gapRatio ^ (2 * N)) * asymptoticEnvelope :=
        mul_le_mul_of_nonneg_left h_central_binomial_asymptotic_certificate
          h_gap_envelope_nonneg
  exact ⟨h_first, h_second, h_central_binomial_asymptotic_certificate⟩

end Omega.Conclusion
