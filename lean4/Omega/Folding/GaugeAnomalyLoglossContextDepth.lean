import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Folding

/-- Paper-facing threshold-depth corollary for the exponential log-loss lower bound:
rearranging `c ≤ ε β^k` and taking logs gives the depth lower bound. -/
theorem paper_fold_gauge_anomaly_logloss_context_depth (beta c eps : Real) (k : Nat)
    (hbeta : 1 < beta) (hc : 0 < c) (heps : 0 < eps) (hgap : c ≤ eps * beta ^ k) :
    Real.log (c / eps) / Real.log beta ≤ (k : Real) := by
  have hbeta_pos : 0 < beta := lt_trans zero_lt_one hbeta
  have hlogbeta_pos : 0 < Real.log beta := Real.log_pos hbeta
  have hdiv : c / eps ≤ beta ^ k := by
    rw [div_le_iff₀ heps]
    simpa [mul_comm] using hgap
  have hlog :
      Real.log (c / eps) ≤ Real.log (beta ^ k) := by
    exact Real.log_le_log (div_pos hc heps) hdiv
  have hlog_pow : Real.log (beta ^ k) = (k : Real) * Real.log beta := by
    rw [Real.log_pow]
  rw [div_le_iff₀ hlogbeta_pos]
  simpa [hlog_pow, mul_comm, mul_left_comm, mul_assoc] using hlog

end Omega.Folding
