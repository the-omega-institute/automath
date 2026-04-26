import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Bit-normalized budget for a natural-log exponent. -/
noncomputable def conclusion_ae_recovery_threshold_drops_to_second_maximum_budget
    (alpha : ℝ) : ℝ :=
  alpha / Real.log 2

/-- Exponent gap left after spending `β` bits per window. -/
noncomputable def conclusion_ae_recovery_threshold_drops_to_second_maximum_successDeficit
    (alpha beta : ℝ) : ℝ :=
  alpha - beta * Real.log 2

/-- Concrete threshold-drop package: when the second maximum exponent is below the top-fiber
exponent, its normalized recovery budget is strictly lower, and any larger bit-rate gives a
negative second-window success deficit. -/
def conclusion_ae_recovery_threshold_drops_to_second_maximum_statement : Prop :=
  ∀ alphaTop alphaSecond beta : ℝ,
    alphaSecond < alphaTop →
      conclusion_ae_recovery_threshold_drops_to_second_maximum_budget alphaSecond < beta →
        conclusion_ae_recovery_threshold_drops_to_second_maximum_budget alphaSecond <
            conclusion_ae_recovery_threshold_drops_to_second_maximum_budget alphaTop ∧
          conclusion_ae_recovery_threshold_drops_to_second_maximum_successDeficit
              alphaSecond beta <
            0

/-- Paper label:
`cor:conclusion-ae-recovery-threshold-drops-to-second-maximum`. -/
theorem paper_conclusion_ae_recovery_threshold_drops_to_second_maximum :
    conclusion_ae_recovery_threshold_drops_to_second_maximum_statement := by
  intro alphaTop alphaSecond beta hdrop hbeta
  have hlog_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_ne : Real.log 2 ≠ 0 := ne_of_gt hlog_pos
  constructor
  · exact (div_lt_div_iff_of_pos_right hlog_pos).2 hdrop
  · have hmul := mul_lt_mul_of_pos_right hbeta hlog_pos
    rw [conclusion_ae_recovery_threshold_drops_to_second_maximum_budget] at hmul
    field_simp [hlog_ne] at hmul
    rw [conclusion_ae_recovery_threshold_drops_to_second_maximum_successDeficit]
    linarith

end Omega.Conclusion
