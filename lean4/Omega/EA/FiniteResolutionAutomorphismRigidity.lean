import Omega.Folding.FiberRing

namespace Omega.EA

/-- Paper label: `cor:finite-resolution-automorphism-rigidity`. -/
theorem paper_finite_resolution_automorphism_rigidity (m : ℕ)
    (f : Omega.X m ≃+* Omega.X m) : f = RingEquiv.refl (Omega.X m) := by
  ext x
  exact Omega.X.ringEquiv_eq_id m f x

end Omega.EA
