import Mathlib.Tactic
import Omega.Folding.FiberArithmeticProperties

namespace Omega.EA.MulNoNewPrimitive

open Omega

/-- Stable multiplication equals iterated stable addition, so multiplication
    need not be introduced as a new primitive.
    cor:mul-no-new-primitive -/
theorem paper_mul_no_new_primitive {m : ℕ} (hm : 1 ≤ m) (x y : X m) :
    X.stableMul y x = X.iteratedStableAdd x (stableValue y) :=
  (X.iteratedStableAdd_eq_stableMul x y hm).symm

end Omega.EA.MulNoNewPrimitive
