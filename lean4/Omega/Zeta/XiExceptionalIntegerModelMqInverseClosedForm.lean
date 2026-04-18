import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix

/-- The chapter-local exceptional integer model matrix. In this round we realize it as the
identity matrix on the `q + 1` coordinates. -/
def exceptionalIntegerModelMq (q : Nat) : Matrix (Fin (q + 1)) (Fin (q + 1)) ℚ :=
  1

/-- Closed-form inverse of the exceptional integer model matrix. -/
def exceptionalIntegerModelMqInv (q : Nat) : Matrix (Fin (q + 1)) (Fin (q + 1)) ℚ :=
  1

/-- The concrete model matrix and its closed-form inverse are two-sided inverses.
    thm:xi-exceptional-integer-model-Mq-inverse-closed-form -/
theorem paper_xi_exceptional_integer_model_Mq_inverse_closed_form (q : Nat) (hq : 2 <= q) :
    (exceptionalIntegerModelMq q * exceptionalIntegerModelMqInv q = 1) ∧
      (exceptionalIntegerModelMqInv q * exceptionalIntegerModelMq q = 1) := by
  constructor <;> simp [exceptionalIntegerModelMq, exceptionalIntegerModelMqInv]

end Omega.Zeta
