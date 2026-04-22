import Mathlib

namespace Omega.Zeta

/-- Paper label: `prop:xi-endpoint-heat-probe-toeplitz-herglotz-identity`. If the endpoint heat
probe moments are represented as integrals of the nonnegative kernel `r(x)^N`, then each
coefficient is nonnegative. -/
theorem paper_xi_endpoint_heat_probe_toeplitz_herglotz_identity
    (μ : MeasureTheory.Measure ℝ) (r : ℝ → ℝ) (a : ℕ → ℝ)
    (hRep : ∀ N, a N = ∫ x, r x ^ N ∂μ) (hr : ∀ x, 0 ≤ r x) :
    ∀ N, 0 ≤ a N := by
  intro N
  rw [hRep N]
  refine MeasureTheory.integral_nonneg_of_ae ?_
  filter_upwards with x
  exact pow_nonneg (hr x) N

end Omega.Zeta
