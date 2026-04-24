import Omega.Folding.FiberRing

namespace Omega.EA

/-- Paper label: `thm:finite-resolution-mod`. The finite-resolution arithmetic on `Omega.X m`
is the ring structure transported from `ZMod (Nat.fib (m + 2))` by the stable-value equivalence. -/
theorem paper_finite_resolution_mod (m : ℕ) :
    Nonempty (Omega.X m ≃+* ZMod (Nat.fib (m + 2))) := by
  exact ⟨Omega.X.stableValueRingEquiv m⟩

end Omega.EA
