import Mathlib.Tactic

namespace Omega.PhysicalSpacetimeSkeleton

/-- Paper-facing wrapper for the clock transport chain after imposing the local exactness
    hypothesis on `dDeltaTau` and identifying the transport curvature with `-dA`.
    thm:physical-spacetime-clock-transport-equation -/
theorem paper_physical_spacetime_clock_transport_equation
    {C : Type*} [AddGroup C] (delta : C → C) (Theta dDeltaTau dA Omega : C)
    (hTheta : delta Theta = dDeltaTau - dA) (hDeltaTau : dDeltaTau = 0)
    (hOmega : Omega = -dA) :
    delta Theta = Omega := by
  calc
    delta Theta = dDeltaTau - dA := hTheta
    _ = 0 - dA := by rw [hDeltaTau]
    _ = -dA := by simp
    _ = Omega := by simpa using hOmega.symm

end Omega.PhysicalSpacetimeSkeleton
