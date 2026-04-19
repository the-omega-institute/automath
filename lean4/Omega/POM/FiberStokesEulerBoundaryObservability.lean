import Mathlib.Tactic

namespace Omega.POM

/-- Concrete finite data for the full-coordinate Walsh sign readout, the corresponding
`Z_x(-1)` specialization, and the reduced Euler characteristic. -/
structure POMFiberStokesEulerBoundaryObservabilityData where
  parity : ℕ
  walshReadout : ℤ
  zAtMinusOne : ℤ
  reducedEulerCharacteristic : ℤ
  hWalshFull :
    walshReadout = ((-1 : ℤ) ^ parity) * zAtMinusOne
  hEulerFromWitten :
    reducedEulerCharacteristic = -zAtMinusOne

/-- Boundary observability packaged as the full-coordinate Walsh sign recovering the Euler
characteristic after the parity correction. -/
def POMFiberStokesEulerBoundaryObservabilityData.eulerCharacteristicBoundaryObservable
    (D : POMFiberStokesEulerBoundaryObservabilityData) : Prop :=
  ((-1 : ℤ) ^ D.parity) * D.reducedEulerCharacteristic = -D.walshReadout

/-- Paper wrapper for the Stokes/Euler boundary observable package.
    cor:pom-fiber-stokes-euler-characteristic-boundary-observable -/
theorem paper_pom_fiber_stokes_euler_characteristic_boundary_observable
    (D : POMFiberStokesEulerBoundaryObservabilityData) : D.eulerCharacteristicBoundaryObservable := by
  dsimp [POMFiberStokesEulerBoundaryObservabilityData.eulerCharacteristicBoundaryObservable]
  rw [D.hEulerFromWitten, D.hWalshFull]
  ring

end Omega.POM
