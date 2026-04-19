import Omega.EA.MulNoNewPrimitive
import Omega.Folding.FiberArithmeticProperties

namespace Omega.EA

open Omega

/-- Stable arithmetic on `X m` is generated from successor iteration alone: addition is the
successor iterate readout, and multiplication is iterated addition.
    cor:primitive-minimal-successor -/
theorem paper_ea_primitive_minimal_successor {m : ℕ} (hm : 1 ≤ m) :
    (∀ x y : X m, (X.stableSucc^[stableValue y]) x = X.stableAdd x y) ∧
      (∀ x y : X m, X.stableMul y x = X.iteratedStableAdd x (stableValue y)) := by
  refine ⟨?_, ?_⟩
  · intro x y
    exact X.stableSucc_iterate_eq_stableAdd x y hm
  · intro x y
    exact Omega.EA.MulNoNewPrimitive.paper_mul_no_new_primitive hm x y

end Omega.EA
