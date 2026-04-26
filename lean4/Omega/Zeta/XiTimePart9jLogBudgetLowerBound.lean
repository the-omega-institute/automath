import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-time-part9j-log-budget-lower-bound`. -/
theorem paper_xi_time_part9j_log_budget_lower_bound {u0 ε : ℝ} (n0 : ℕ) (hu0 : 0 < u0)
    (hε0 : 0 < ε) (hε1 : ε < 1) (herr : (u0 / (1 + u0)) ^ n0 ≤ ε) :
    Real.log (1 / ε) / Real.log ((1 + u0) / u0) ≤ (n0 : ℝ) := by
  have hden_pos : 0 < 1 + u0 := by linarith
  have hratio_pos : 0 < u0 / (1 + u0) := div_pos hu0 hden_pos
  have hratio_lt_one : u0 / (1 + u0) < 1 := by
    rw [div_lt_one hden_pos]
    linarith
  have hpow_pos : 0 < (u0 / (1 + u0)) ^ n0 := pow_pos hratio_pos n0
  have hlog_le : Real.log ((u0 / (1 + u0)) ^ n0) ≤ Real.log ε :=
    Real.log_le_log hpow_pos herr
  have hlog_pow :
      Real.log ((u0 / (1 + u0)) ^ n0) =
        (n0 : ℝ) * Real.log (u0 / (1 + u0)) := by
    rw [Real.log_pow]
  have hneg :
      -Real.log ε ≤ (n0 : ℝ) * Real.log ((1 + u0) / u0) := by
    rw [hlog_pow] at hlog_le
    have hrecip :
        Real.log ((1 + u0) / u0) = -Real.log (u0 / (1 + u0)) := by
      have hinv_eq : (u0 / (1 + u0))⁻¹ = (1 + u0) / u0 := by
        field_simp [hu0.ne', hden_pos.ne']
      rw [← hinv_eq, Real.log_inv]
    have hneg0 :
        -Real.log ε ≤ -((n0 : ℝ) * Real.log (u0 / (1 + u0))) := by
      linarith
    calc
      -Real.log ε ≤ (n0 : ℝ) * (-Real.log (u0 / (1 + u0))) := by
        linarith
      _ = (n0 : ℝ) * Real.log ((1 + u0) / u0) := by rw [hrecip]
  have hbase_gt_one : 1 < (1 + u0) / u0 := by
    rw [one_lt_div hu0]
    linarith
  have hlog_den_pos : 0 < Real.log ((1 + u0) / u0) := Real.log_pos hbase_gt_one
  have hlog_inv : Real.log (1 / ε) = -Real.log ε := by
    rw [one_div, Real.log_inv]
  rw [hlog_inv]
  exact (div_le_iff₀ hlog_den_pos).2 hneg

end Omega.Zeta
