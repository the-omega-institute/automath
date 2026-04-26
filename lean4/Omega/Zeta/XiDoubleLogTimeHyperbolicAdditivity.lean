import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-double-log-time-hyperbolic-additivity`.
Once the reciprocal depth scale is rewritten as `exp d`, a product lower bound becomes additive on
the logarithmic scale. -/
theorem paper_xi_double_log_time_hyperbolic_additivity
    {m N h d : ℝ} (hm : 1 ≤ m) (hN : 1 ≤ N) (hdepth : h⁻¹ = Real.exp d) (hprod : h⁻¹ ≤ m * N) :
    d ≤ Real.log m + Real.log N := by
  have hm_pos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hN_pos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hexp_le : Real.exp d ≤ m * N := by
    simpa [hdepth] using hprod
  have hlog_le :
      Real.log (Real.exp d) ≤ Real.log (m * N) := Real.log_le_log (Real.exp_pos d) hexp_le
  simpa [Real.log_exp, Real.log_mul hm_pos.ne' hN_pos.ne', add_comm, add_left_comm, add_assoc] using
    hlog_le

end Omega.Zeta
