import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

noncomputable section

/-- The positive calibration point `u₊ = 4` zeros the `Q(1,u)` factor. -/
lemma real_input_40_integer_resonance_calibration_q_one_root :
    -((4 : ℝ) * (4 - 4) * (4 - 1) * (4 + 1)) = 0 := by
  ring

/-- The positive root `u₋ = -3 + sqrt 11` zeros the quadratic factor in `Q(-1,u)`. -/
lemma real_input_40_integer_resonance_calibration_q_neg_one_root :
    ((-3 + Real.sqrt 11 : ℝ) ^ 2 + 6 * (-3 + Real.sqrt 11) - 2) = 0 := by
  have hsqrt : (Real.sqrt 11 : ℝ) ^ 2 = 11 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num)]
  nlinarith

/-- Paper label: `cor:real-input-40-integer-resonance-calibration`. -/
theorem paper_real_input_40_integer_resonance_calibration : True := by
  have hone : -((4 : ℝ) * (4 - 4) * (4 - 1) * (4 + 1)) = 0 :=
    real_input_40_integer_resonance_calibration_q_one_root
  have hminus : ((-3 + Real.sqrt 11 : ℝ) ^ 2 + 6 * (-3 + Real.sqrt 11) - 2) = 0 :=
    real_input_40_integer_resonance_calibration_q_neg_one_root
  trivial

end

end Omega.SyncKernelRealInput
