import Mathlib.Data.Complex.Basic
import Omega.SyncKernelWeighted.PrimitiveCompletionHatp

namespace Omega.SyncKernelWeighted

open Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- The completed primitive value at the half-turn specialization `s = 0`. -/
def primitive_halfturn_sign_law_completed_value (m : ℕ) : ℚ :=
  completionEval (primitive_completion_hatp_completed_poly (2 * m)) 0

/-- Undo the completion factor at the half-turn point `r = I`, so `u = r^2 = -1`. -/
def primitive_halfturn_sign_law_primitive_value (m : ℕ) : ℂ :=
  (Complex.I : ℂ) ^ (2 * m) * primitive_halfturn_sign_law_completed_value m

/-- The half-turn specialization of the primitive completion law records that the completion
factor `r ^ (-2m)` contributes the sign `(-1)^m` when `r = I`. -/
def primitive_halfturn_sign_law_statement (m : ℕ) : Prop :=
  primitive_halfturn_sign_law_primitive_value m =
    ((-1 : ℂ) ^ m) * primitive_halfturn_sign_law_completed_value m

/-- Paper label: `cor:primitive-halfturn-sign-law`. -/
theorem paper_primitive_halfturn_sign_law (m : ℕ) : primitive_halfturn_sign_law_statement m := by
  simp [primitive_halfturn_sign_law_statement, primitive_halfturn_sign_law_primitive_value,
    primitive_halfturn_sign_law_completed_value, pow_mul, Complex.I_sq]

end

end Omega.SyncKernelWeighted
