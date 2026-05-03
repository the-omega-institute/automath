import Omega.Folding.CollisionKernel

namespace Omega

/-- Paper wrapper for the signed-companion Bowen-Franks determinant.
    thm:signed-companion-det -/
theorem paper_signed_companion_det {R : Type*} [CommRing R] {n : ℕ}
    (c : Fin (n + 1) → R) :
    ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) - signedCompanion c).det =
      1 + ∑ i, c i := by
  simpa using signedCompanionDet c

end Omega
