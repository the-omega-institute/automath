import Omega.Conclusion.EndpointHorizonArcsineKLClosedForm
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The endpoint-horizon KL divergence differs from the logarithmic scale cost by at most one bit.
    cor:conclusion-endpoint-horizon-kl-vs-log-cost-onebit -/
theorem paper_conclusion_endpoint_horizon_kl_vs_log_cost_onebit (a b : ℝ) (ha : 0 < a)
    (hab : a ≤ b) : Real.log (b / a) ≤ endpointHorizonKL a b ∧
      endpointHorizonKL a b ≤ Real.log (2 * (b / a)) := by
  let ρ : ℝ := b / a
  have hclosed : endpointHorizonKL a b = Real.arcosh ρ := by
    simpa [ρ] using paper_conclusion_endpoint_horizon_arcsine_kl_closed_form a b ha hab
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    exact div_pos (lt_of_lt_of_le ha hab) ha
  have hρ_ge_one : 1 ≤ ρ := by
    dsimp [ρ]
    have hdiv : a / a ≤ b / a := div_le_div_of_nonneg_right hab ha.le
    simpa [ha.ne'] using hdiv
  have hsq_nonneg : 0 ≤ ρ ^ 2 - 1 := by
    nlinarith
  have hsqrt_nonneg : 0 ≤ Real.sqrt (ρ ^ 2 - 1) := Real.sqrt_nonneg _
  have hsqrt_le : Real.sqrt (ρ ^ 2 - 1) ≤ ρ := by
    nlinarith [Real.sq_sqrt hsq_nonneg, hρ_pos, hsqrt_nonneg]
  have harcosh : endpointHorizonKL a b = Real.log (ρ + Real.sqrt (ρ ^ 2 - 1)) := by
    rw [hclosed, Real.arcosh]
  have harg_pos : 0 < ρ + Real.sqrt (ρ ^ 2 - 1) := by
    positivity
  have hlower : ρ ≤ ρ + Real.sqrt (ρ ^ 2 - 1) := by
    linarith
  have hupper : ρ + Real.sqrt (ρ ^ 2 - 1) ≤ 2 * ρ := by
    linarith
  constructor
  · rw [harcosh]
    exact Real.log_le_log hρ_pos hlower
  · rw [harcosh]
    exact Real.log_le_log harg_pos hupper

end Omega.Conclusion
