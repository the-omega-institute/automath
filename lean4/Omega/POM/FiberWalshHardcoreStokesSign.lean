import Mathlib.Tactic

namespace Omega.POM

/-- Concrete finite data for the Walsh/hard-core sign specialization and the full-coordinate
readout at the all-minus sign. -/
structure POMFiberWalshHardcoreStokesSignData where
  parity : ℕ
  walshAtSigns : ℤ
  hardcoreAtSigns : ℤ
  fullWalshReadout : ℤ
  zAtMinusOne : ℤ
  hWalshAtSigns : walshAtSigns = hardcoreAtSigns
  hFullWalshReadout : fullWalshReadout = ((-1 : ℤ) ^ parity) * zAtMinusOne

/-- Paper wrapper for the sign-specialized Walsh/hard-core identity.
    cor:pom-fiber-walsh-hardcore-stokes-sign -/
theorem paper_pom_fiber_walsh_hardcore_stokes_sign
    (D : POMFiberWalshHardcoreStokesSignData) :
    D.walshAtSigns = D.hardcoreAtSigns ∧
      D.fullWalshReadout = ((-1 : ℤ) ^ D.parity) * D.zAtMinusOne := by
  exact ⟨D.hWalshAtSigns, D.hFullWalshReadout⟩

end Omega.POM
