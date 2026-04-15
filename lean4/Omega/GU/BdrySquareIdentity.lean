import Mathlib.Tactic
import Mathlib.Data.Nat.Fib.Basic
import Omega.Folding.BoundaryLayer

namespace Omega.GU.BdrySquareIdentity

open Omega

/-- Boundary layer square identity at m=6: b(11) = b(6)^2 + b(7)^2 = 34.
    cor:bdry-m6-square-instance -/
theorem paper_bdry_m6_square_instance :
    cBoundaryCount 11 = cBoundaryCount 6 ^ 2 + cBoundaryCount 7 ^ 2 ∧
    cBoundaryCount 6 = 3 ∧ cBoundaryCount 7 = 5 ∧ cBoundaryCount 11 = 34 ∧
    Nat.fib 9 = Nat.fib 4 ^ 2 + Nat.fib 5 ^ 2 ∧
    3 ^ 2 + 5 ^ 2 = 34 := by
  rw [cBoundaryCount_eq_fib_general 11 (by omega),
      cBoundaryCount_eq_fib_general 6 (by omega),
      cBoundaryCount_eq_fib_general 7 (by omega)]
  simp [Nat.fib_add_two]

end Omega.GU.BdrySquareIdentity
