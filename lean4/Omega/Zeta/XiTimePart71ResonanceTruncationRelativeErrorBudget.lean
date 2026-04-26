import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

theorem paper_xi_time_part71_resonance_truncation_relative_error_budget
    (epsilon C Ctrunc tail : Real) (heps : 0 < epsilon) (hCpos : 0 < C)
    (htail_nonneg : 0 ≤ tail)
    (htrunc : Ctrunc * Real.exp (-tail) ≤ C ∧ C ≤ Ctrunc)
    (htail : tail ≤ Real.log (1 + epsilon)) :
    1 ≤ Ctrunc / C ∧ Ctrunc / C ≤ 1 + epsilon := by
  have _ : 0 ≤ tail := htail_nonneg
  have hC_nonneg : 0 ≤ C := hCpos.le
  have hleft : Ctrunc * Real.exp (-tail) ≤ C := htrunc.1
  have hright : C ≤ Ctrunc := htrunc.2
  constructor
  · calc
      1 = C / C := by rw [div_self hCpos.ne']
      _ ≤ Ctrunc / C := div_le_div_of_nonneg_right hright hC_nonneg
  · have hCtrunc_le : Ctrunc ≤ C * Real.exp tail := by
      calc
        Ctrunc = (Ctrunc * Real.exp (-tail)) * Real.exp tail := by
          rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
        _ ≤ C * Real.exp tail :=
          mul_le_mul_of_nonneg_right hleft (Real.exp_pos tail).le
    have hratio_exp : Ctrunc / C ≤ Real.exp tail := by
      calc
        Ctrunc / C ≤ (C * Real.exp tail) / C :=
          div_le_div_of_nonneg_right hCtrunc_le hC_nonneg
        _ = Real.exp tail := by field_simp [hCpos.ne']
    have hlog_pos : 0 < 1 + epsilon := by linarith
    have hexp_tail : Real.exp tail ≤ 1 + epsilon := by
      rw [← Real.exp_log hlog_pos, Real.exp_le_exp]
      exact htail
    exact hratio_exp.trans hexp_tail

end Omega.Zeta
