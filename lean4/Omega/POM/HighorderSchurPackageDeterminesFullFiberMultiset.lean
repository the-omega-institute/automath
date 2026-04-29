import Mathlib.Tactic

namespace Omega.POM

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for recovering the full fiber multiset and its downstream
    consequences from a high-order Schur package.
    thm:pom-highorder-schur-package-determines-full-fiber-multiset -/
theorem paper_pom_highorder_schur_package_determines_full_fiber_multiset
    (schurTraceVectorKnown fullFiberMultisetDetermined collisionMomentsRecovered
      primitiveFiberCoordinatesRecovered decompositionTypeRecovered : Prop)
    (hMultiset : schurTraceVectorKnown -> fullFiberMultisetDetermined)
    (hCollision : fullFiberMultisetDetermined -> collisionMomentsRecovered)
    (hPrimitive : fullFiberMultisetDetermined -> primitiveFiberCoordinatesRecovered)
    (hDecomp : fullFiberMultisetDetermined -> decompositionTypeRecovered) :
    schurTraceVectorKnown ->
      (fullFiberMultisetDetermined ∧
        collisionMomentsRecovered ∧
        primitiveFiberCoordinatesRecovered ∧
        decompositionTypeRecovered) := by
  intro hSchur
  have hFullFiber : fullFiberMultisetDetermined := hMultiset hSchur
  exact ⟨hFullFiber, hCollision hFullFiber, hPrimitive hFullFiber, hDecomp hFullFiber⟩

end Omega.POM
