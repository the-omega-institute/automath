import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Omega.Zeta.XiEndpointFluxFiniteCMVComputable

namespace Omega.Zeta

/-- Paper label: `cor:xi-endpoint-flux-log-sample-complexity`. -/
theorem paper_xi_endpoint_flux_log_sample_complexity
    (D : xi_endpoint_flux_finite_cmv_computable_data) (eps : ℝ) (N : ℕ) (heps : 0 < eps)
    (hC : 0 < D.C)
    (hN : Real.log (D.C / eps) / Real.log (1 / D.q) ≤ (N : ℝ)) :
    |D.truncatedFlux N - D.exactFlux N| ≤ eps := by
  rcases paper_xi_endpoint_flux_finite_cmv_computable D with ⟨_, hgeom, _⟩
  rcases hgeom with ⟨_, hq_pos, hq_lt_one, herror⟩
  have hbase_pos : 0 < 1 / D.q := one_div_pos.mpr hq_pos
  have hbase_gt_one : 1 < 1 / D.q := one_lt_one_div hq_pos hq_lt_one
  have hlog_pos : 0 < Real.log (1 / D.q) := Real.log_pos hbase_gt_one
  have hlog_bound : Real.log (D.C / eps) ≤ (N : ℝ) * Real.log (1 / D.q) := by
    have := (div_le_iff₀ hlog_pos).1 hN
    simpa [mul_comm] using this
  have hratio_le : D.C / eps ≤ (1 / D.q) ^ N := by
    have hexp := Real.exp_le_exp.mpr hlog_bound
    calc
      D.C / eps = Real.exp (Real.log (D.C / eps)) := by
        rw [Real.exp_log (div_pos hC heps)]
      _ ≤ Real.exp ((N : ℝ) * Real.log (1 / D.q)) := hexp
      _ = (1 / D.q) ^ N := by
        rw [← Real.log_rpow hbase_pos, Real.rpow_natCast,
          Real.exp_log (pow_pos hbase_pos N)]
  have hratio_le' : D.C / eps ≤ (D.q ^ N)⁻¹ := by
    simpa [one_div, inv_pow] using hratio_le
  have hC_le_div : D.C ≤ eps / D.q ^ N := by
    have := (div_le_iff₀ heps).1 hratio_le'
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  have hpow_pos : 0 < D.q ^ N := pow_pos hq_pos N
  have hthreshold : D.C * D.q ^ N ≤ eps := (le_div_iff₀ hpow_pos).1 hC_le_div
  exact (herror N).trans hthreshold

end Omega.Zeta
