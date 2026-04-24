import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Scalar amplitude defect: vanishing means the logarithmic modulus carries no residual
amplitude information. -/
def amp_defect_unitary_amplitudeDefect (T : ℂ) : ℝ :=
  |Real.log ‖T‖|

/-- In the scalar wrapper, unitarity means that the modulus is exactly `1`. -/
def amp_defect_unitary_isUnitary (T : ℂ) : Prop :=
  ‖T‖ = 1

/-- Concrete statement: for nonzero modulus, vanishing amplitude defect is equivalent to scalar
unitarity. -/
def amp_defect_unitary_statement : Prop :=
  ∀ T : ℂ, 0 < ‖T‖ →
    (amp_defect_unitary_amplitudeDefect T = 0 ↔ amp_defect_unitary_isUnitary T)

lemma amp_defect_unitary_logAbs_eq_zero_of_amplitudeDefect_eq_zero {T : ℂ}
    (hDefect : amp_defect_unitary_amplitudeDefect T = 0) :
    Real.log ‖T‖ = 0 := by
  simpa [amp_defect_unitary_amplitudeDefect] using abs_eq_zero.mp hDefect

lemma amp_defect_unitary_abs_eq_one_of_logAbs_eq_zero {T : ℂ}
    (hPos : 0 < ‖T‖) (hLog : Real.log ‖T‖ = 0) :
    ‖T‖ = 1 := by
  have hExp := congrArg Real.exp hLog
  simpa [Real.exp_log hPos, Real.exp_zero] using hExp

lemma amp_defect_unitary_isUnitary_of_abs_eq_one {T : ℂ} (hAbs : ‖T‖ = 1) :
    amp_defect_unitary_isUnitary T := hAbs

/-- Paper label: `prop:amp-defect-unitary`. -/
theorem paper_amp_defect_unitary : amp_defect_unitary_statement := by
  intro T hPos
  constructor
  · intro hDefect
    have hLog :
        Real.log ‖T‖ = 0 :=
      amp_defect_unitary_logAbs_eq_zero_of_amplitudeDefect_eq_zero hDefect
    have hAbs :
        ‖T‖ = 1 :=
      amp_defect_unitary_abs_eq_one_of_logAbs_eq_zero hPos hLog
    exact amp_defect_unitary_isUnitary_of_abs_eq_one hAbs
  · intro hUnitary
    rw [amp_defect_unitary_isUnitary] at hUnitary
    rw [amp_defect_unitary_amplitudeDefect, hUnitary]
    norm_num

end

end Omega.Zeta
