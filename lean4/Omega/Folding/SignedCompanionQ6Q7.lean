import Mathlib.Tactic
import Omega.Folding.CollisionKernel

namespace Omega

/-- Paper wrapper for the audited `q = 6, 7` signed-companion determinants and their
Fibonacci baseline excesses.
    cor:signed-companion-q6-q7 -/
theorem paper_signed_companion_q6_q7 :
    ((1 : Matrix (Fin 7) (Fin 7) ℤ) - signedCompanion signedCompanionCoeffs6).det = 110 ∧
    ((1 : Matrix (Fin 7) (Fin 7) ℤ) - signedCompanion signedCompanionCoeffs7).det = 422 ∧
    110 - (Nat.fib 10 : ℤ) = 55 ∧
    422 - (Nat.fib 12 : ℤ) = 278 := by
  refine ⟨signedCompanionDet6, signedCompanionDet7, ?_, ?_⟩ <;> norm_num [Nat.fib]

end Omega
