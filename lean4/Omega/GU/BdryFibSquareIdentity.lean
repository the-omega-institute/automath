import Mathlib.Tactic
import Omega.Folding.BoundaryLayer

namespace Omega.GU.BdryFibSquareIdentity

open Omega

/-- Paper label: `prop:bdry-fib-square-identity`. -/
theorem paper_bdry_fib_square_identity (m : Nat) (hm : 2 <= m) :
    Omega.cBoundaryCount (2 * m - 1) =
      Omega.cBoundaryCount m ^ 2 + Omega.cBoundaryCount (m + 1) ^ 2 := by
  simpa using Omega.cBoundaryCount_square_identity_general' m hm

end Omega.GU.BdryFibSquareIdentity
