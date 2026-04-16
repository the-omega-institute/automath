import Mathlib.Tactic

namespace Omega.PhysicalSpacetimeSkeleton

/-- Paper-facing curvature closure package for the clock-difference relation: the clock
    difference is `delta`-closed by hypothesis, the transport curvature is identified with
    `-delta A`, and the resulting curvature is itself `delta`-closed because `delta² A = 0`.
    prop:physical-spacetime-clock-difference-and-transport-curvature -/
theorem paper_physical_spacetime_clock_difference_and_transport_curvature
    {C : Type*} [AddGroup C] (delta : C →+ C) (DeltaTau A Omega : C)
    (hDeltaTau : delta DeltaTau = 0) (hOmega : Omega = -delta A)
    (hDeltaSq : delta (delta A) = 0) :
    delta DeltaTau = 0 ∧ Omega = -delta A ∧ delta Omega = 0 := by
  refine ⟨hDeltaTau, hOmega, ?_⟩
  rw [hOmega, map_neg, hDeltaSq]
  simp

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
