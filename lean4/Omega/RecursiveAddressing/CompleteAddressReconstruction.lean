import Omega.RecursiveAddressing.InverseLimitDeterminacy

namespace Omega.RecursiveAddressing

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: complete address data reconstructs the visible point exactly, and the
    inverse-limit reconstruction maps are mutually inverse.
    thm:complete-address-reconstruction -/
theorem paper_scan_projection_address_complete_address_reconstruction_seeds :
    Function.LeftInverse (Omega.X.toFamily : Omega.X.XInfinity → Omega.X.CompatibleFamily)
      (Omega.X.ofFamily : Omega.X.CompatibleFamily → Omega.X.XInfinity) ∧
    Function.RightInverse (Omega.X.toFamily : Omega.X.XInfinity → Omega.X.CompatibleFamily)
      (Omega.X.ofFamily : Omega.X.CompatibleFamily → Omega.X.XInfinity) ∧
    Function.Bijective (Omega.X.toFamily : Omega.X.XInfinity → Omega.X.CompatibleFamily) := by
  refine ⟨?_, ?_, Omega.X.inverseLimitEquiv.symm.bijective⟩
  · intro F
    exact Omega.X.toFamily_ofFamily F
  · intro a
    exact Omega.X.ofFamily_toFamily a

/-- Packaged form of the complete-address reconstruction seed.
    thm:complete-address-reconstruction -/
theorem paper_scan_projection_address_complete_address_reconstruction_package :
    Function.LeftInverse (Omega.X.toFamily : Omega.X.XInfinity → Omega.X.CompatibleFamily)
      (Omega.X.ofFamily : Omega.X.CompatibleFamily → Omega.X.XInfinity) ∧
    Function.RightInverse (Omega.X.toFamily : Omega.X.XInfinity → Omega.X.CompatibleFamily)
      (Omega.X.ofFamily : Omega.X.CompatibleFamily → Omega.X.XInfinity) ∧
    Function.Bijective (Omega.X.toFamily : Omega.X.XInfinity → Omega.X.CompatibleFamily) :=
  paper_scan_projection_address_complete_address_reconstruction_seeds

end Omega.RecursiveAddressing
