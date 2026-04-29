import Omega.Folding.FiberArithmeticProperties

namespace Omega.EA

/-- Concrete finite-resolution data for reading multiplication from successor-iterated addition. -/
structure mul_from_successor_data where
  m : ℕ
  hm : 1 ≤ m
  x : Omega.X m
  y : Omega.X m

namespace mul_from_successor_data

/-- Multiplication by `y` is obtained by iterating addition of `x` `stableValue y` times. -/
def successor_mul_eq_stable_mul (D : mul_from_successor_data) : Prop :=
  Omega.X.iteratedStableAdd D.x (Omega.stableValue D.y) = Omega.X.stableMul D.y D.x

end mul_from_successor_data

/-- Paper label: `thm:mul-from-successor`. Stable multiplication is successor-generated. -/
theorem paper_mul_from_successor (D : mul_from_successor_data) :
    D.successor_mul_eq_stable_mul := by
  exact Omega.stableMul_from_successor D.x D.y D.hm

end Omega.EA
