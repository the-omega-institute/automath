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

/-- Local-patch version of the local clock-potential existence statement. -/
theorem local_clock_potential_of_transport_flat_exact_patch
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

/-- Paper-facing wrapper for the existence of a local clock potential on a transport-flat exact
    patch: the transport equation makes `Θ|_U` closed when `Ω|_U = 0`, and exactness upgrades
    closedness to a potential.
    thm:physical-spacetime-local-clock-potential -/
theorem paper_physical_spacetime_local_clock_potential
    {C : Type*} [AddGroup C]
    (delta : C → C) (ThetaU dDeltaTau dA OmegaU : C)
    (hTheta : delta ThetaU = dDeltaTau - dA)
    (hDeltaTau : dDeltaTau = 0)
    (hOmega : OmegaU = -dA)
    (hFlat : OmegaU = 0)
    (hExact : delta ThetaU = 0 → ∃ φU : C, delta φU = ThetaU) :
    ∃ φU : C, ThetaU = delta φU := by
  have hTransport : delta ThetaU = OmegaU :=
    paper_physical_spacetime_clock_transport_equation delta ThetaU dDeltaTau dA OmegaU
      hTheta hDeltaTau hOmega
  have hClosed : delta ThetaU = 0 := by
    calc
      delta ThetaU = OmegaU := hTransport
      _ = 0 := hFlat
  rcases hExact hClosed with ⟨φU, hPotential⟩
  exact ⟨φU, hPotential.symm⟩

end Omega.PhysicalSpacetimeSkeleton
