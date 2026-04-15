import Mathlib.Tactic
import Omega.PhysicalSpacetimeSkeleton.ClockTransportEquation

namespace Omega.PhysicalSpacetimeSkeleton

universe u v

/-- A minimal local patch package: restriction commutes with the `1`-cochain coboundary, every
closed restricted `1`-cochain is exact, and the local potential is produced by the `0`-cochain
coboundary `dZero`. -/
structure TransportFlatExactPatch (OneCochain : Type u) (ZeroCochain : Type v)
    [AddGroup OneCochain] where
  restrict : OneCochain → OneCochain
  dOne : OneCochain → OneCochain
  dZero : ZeroCochain → OneCochain
  restrict_dOne : ∀ θ, dOne (restrict θ) = restrict (dOne θ)
  exact_of_closed : ∀ θ, dOne θ = 0 → ∃ φ : ZeroCochain, θ = dZero φ

/-- On a transport-flat exact patch, the restricted clock transport cocycle is closed by the
existing clock-transport equation, hence exact and therefore admits a local potential.
    thm:physical-spacetime-local-clock-potential -/
theorem paper_physical_spacetime_local_clock_potential
    {OneCochain : Type u} {ZeroCochain : Type v} [AddGroup OneCochain]
    (U : TransportFlatExactPatch OneCochain ZeroCochain)
    (Theta dDeltaTau dA Omega : OneCochain)
    (hTheta : U.dOne Theta = dDeltaTau - dA) (hDeltaTau : dDeltaTau = 0) (hOmega : Omega = -dA)
    (hFlat : U.restrict Omega = 0) :
    ∃ φ : ZeroCochain, U.restrict Theta = U.dZero φ := by
  have hTransport : U.dOne Theta = Omega :=
    paper_physical_spacetime_clock_transport_equation
      (delta := U.dOne) (Theta := Theta) (dDeltaTau := dDeltaTau) (dA := dA) (Omega := Omega)
      hTheta hDeltaTau hOmega
  have hClosed : U.dOne (U.restrict Theta) = 0 := by
    rw [U.restrict_dOne, hTransport, hFlat]
  exact U.exact_of_closed (U.restrict Theta) hClosed

end Omega.PhysicalSpacetimeSkeleton
