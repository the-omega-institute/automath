import Omega.Folding.FiberArithmeticProperties

namespace Omega.EA

open Omega

/-- Paper-facing corollary packaging finite-resolution addition as successor iteration.
    cor:add-from-successor -/
theorem paper_add_from_successor {m : ℕ} (hm : 1 ≤ m) :
    ∀ x y : Omega.X m, (Omega.X.stableSucc^[Omega.stableValue y]) x = Omega.X.stableAdd x y := by
  intro x y
  exact Omega.X.stableSucc_iterate_eq_stableAdd x y hm

end Omega.EA
