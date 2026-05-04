import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-time-part9f-alphabet-threshold`. -/
theorem paper_xi_time_part9f_alphabet_threshold (alpha c M : ℝ) (halpha : 0 < alpha)
    (hc : 0 ≤ c) (hM : 1 < M) (hbudget : c / Real.log M ≤ alpha) :
    Real.exp (c / alpha) ≤ M := by
  have hlog_pos : 0 < Real.log M := Real.log_pos hM
  have hM_pos : 0 < M := lt_trans zero_lt_one hM
  have hbudget_and_nonneg : c / Real.log M ≤ alpha ∧ 0 ≤ c := ⟨hbudget, hc⟩
  have hmul : c ≤ alpha * Real.log M := by
    have hbudget' : c / Real.log M ≤ alpha := hbudget_and_nonneg.1
    rw [div_le_iff₀ hlog_pos] at hbudget'
    linarith
  have hdiv : c / alpha ≤ Real.log M := by
    rw [div_le_iff₀ halpha]
    linarith [hmul]
  calc
    Real.exp (c / alpha) ≤ Real.exp (Real.log M) := Real.exp_le_exp.mpr hdiv
    _ = M := Real.exp_log hM_pos

end Omega.Zeta
