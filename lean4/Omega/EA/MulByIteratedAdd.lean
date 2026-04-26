import Omega.Folding.FiberArithmeticProperties

namespace Omega.EA

/-- Paper-facing corollary: stable multiplication is iterated stable addition.
    thm:mul-by-iterated-add -/
theorem paper_mul_by_iterated_add {m : ℕ} (hm : 1 ≤ m) (c d : Omega.X m) :
    Omega.X.iteratedStableAdd c (Omega.stableValue d) = Omega.X.stableMul d c := by
  simpa using Omega.X.iteratedStableAdd_eq_stableMul c d hm

end Omega.EA
