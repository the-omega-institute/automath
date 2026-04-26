import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.SyncKernelWeighted.LambdaExtremeAsymp

namespace Omega.SyncKernelWeighted

noncomputable section

/-- The low-temperature order-`4` endpoint-density series read off from the Perron branch. -/
def alpha_endpoint_series_low (u : ℝ) : ℝ :=
  3 * u - 5 * u ^ 2 - 114 * u ^ 3 + 1103 * u ^ 4

/-- The mirrored high-temperature order-`4` endpoint-density series. -/
def alpha_endpoint_series_high (u : ℝ) : ℝ :=
  1 - 3 / u + 5 / u ^ 2 + 114 / u ^ 3 - 1103 / u ^ 4

/-- The order-`5` residual left after dividing `u λ'(u)` by the Perron branch. -/
def alpha_endpoint_series_residual (u : ℝ) : ℝ :=
  -3757 - 6095 * u + 63121 * u ^ 2 - 173171 * u ^ 3

/-- The numerator `u λ'(u)` attached to the explicit quartic Perron branch. -/
def alpha_endpoint_series_lambda_derivative_numerator (u : ℝ) : ℝ :=
  u * (3 + 4 * u - 123 * u ^ 2 + 628 * u ^ 3)

/-- Paper label: `cor:alpha-endpoint-series`. The explicit Perron branch from
`paper_lambda_extreme_asymp` yields the low-temperature endpoint-density expansion up to order
`4`, with an exact order-`5` residual, and the high-temperature series is its mirror under
`u ↦ 1 / u`. -/
theorem paper_alpha_endpoint_series :
    (∀ u : ℝ,
      lambdaExtremePerronBranch u = 1 + 3 * u + 2 * u ^ 2 - 41 * u ^ 3 + 157 * u ^ 4) ∧
      (∀ u : ℝ,
        alpha_endpoint_series_lambda_derivative_numerator u =
          lambdaExtremePerronBranch u * alpha_endpoint_series_low u +
            u ^ 5 * alpha_endpoint_series_residual u) ∧
      (∀ u : ℝ, u ≠ 0 →
        alpha_endpoint_series_high u = 1 - alpha_endpoint_series_low (1 / u)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (paper_lambda_extreme_asymp).2.2.1
  · intro u
    have hbranch : lambdaExtremePerronBranch u = 1 + 3 * u + 2 * u ^ 2 - 41 * u ^ 3 + 157 * u ^ 4 :=
      (paper_lambda_extreme_asymp).2.2.1 u
    rw [hbranch]
    unfold alpha_endpoint_series_lambda_derivative_numerator
      alpha_endpoint_series_low alpha_endpoint_series_residual
    ring
  · intro u hu
    unfold alpha_endpoint_series_high alpha_endpoint_series_low
    field_simp [hu]
    ring

end

end Omega.SyncKernelWeighted
