import Omega.SPG.CubeLinftyPrimitiveExplicitMinimizer

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the cube `L^∞` primitive rigidity package: starting from the
boundary Stokes identity and sharp face bounds, equality is forced on each face term and the
pulled-back face forms become the stated rigid coordinate-volume traces.
    thm:spg-cube-linfty-primitive-boundary-rigidity -/
theorem paper_spg_cube_linfty_primitive_boundary_rigidity
    (explicitPrimitive exactDerivative exactSupNorm canonicalBoundaryTrace rigidBoundaryTrace
      facewiseEquality constantFaceVolumeForm : Prop)
    (hBoundary : exactDerivative → exactSupNorm → canonicalBoundaryTrace)
    (hRigid : canonicalBoundaryTrace → rigidBoundaryTrace)
    (hEquality : canonicalBoundaryTrace → facewiseEquality)
    (hVolume : facewiseEquality → constantFaceVolumeForm) :
    explicitPrimitive →
      exactDerivative →
        exactSupNorm →
          explicitPrimitive ∧ exactDerivative ∧ exactSupNorm ∧ canonicalBoundaryTrace ∧
            rigidBoundaryTrace ∧ facewiseEquality ∧ constantFaceVolumeForm := by
  intro hPrimitive hDerivative hNorm
  rcases
      paper_spg_cube_linfty_primitive_explicit_minimizer
        explicitPrimitive exactDerivative exactSupNorm canonicalBoundaryTrace rigidBoundaryTrace
        hBoundary hRigid hPrimitive hDerivative hNorm
    with ⟨hPrimitive', hDerivative', hNorm', hTrace, hRigidTrace⟩
  have hFaces : facewiseEquality := hEquality hTrace
  exact
    ⟨hPrimitive', hDerivative', hNorm', hTrace, hRigidTrace, hFaces, hVolume hFaces⟩

end Omega.SPG
