import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-dirichlet-minimal-character-trigger`. -/
theorem paper_conclusion_dirichlet_minimal_character_trigger (rho lambda phi beta : Real)
    (hlambda : lambda = phi ^ 2) (hphi : 1 < phi) (hrho : phi < rho)
    (hbeta : beta = Real.log rho / Real.log lambda) :
    beta > (1 / 2 : Real) := by
  have hphi_pos : 0 < phi := lt_trans zero_lt_one hphi
  have hlog_phi_pos : 0 < Real.log phi := Real.log_pos hphi
  have hlog_rho_gt : Real.log phi < Real.log rho := Real.log_lt_log hphi_pos hrho
  have hlog_lambda : Real.log lambda = 2 * Real.log phi := by
    rw [hlambda, Real.log_pow]
    norm_num
  rw [hbeta, hlog_lambda]
  have hden_pos : 0 < 2 * Real.log phi := by positivity
  have hhalf : (1 / 2 : Real) = Real.log phi / (2 * Real.log phi) := by
    field_simp [hlog_phi_pos.ne']
  rw [gt_iff_lt, hhalf]
  exact div_lt_div_of_pos_right hlog_rho_gt hden_pos

end Omega.Conclusion
