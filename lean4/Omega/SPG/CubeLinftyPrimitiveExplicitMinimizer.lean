import Omega.SPG.ExplicitMinimizer

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the cube `L^∞` explicit primitive minimizer: the explicit primitive,
its exact derivative, the sharp sup norm, and the rigid boundary trace are packaged together by
combining the existing explicit-minimizer and boundary-rigidity wrappers.
    cor:spg-cube-linfty-primitive-explicit-minimizer -/
theorem paper_spg_cube_linfty_primitive_explicit_minimizer
    (explicitPrimitive exactDerivative exactSupNorm canonicalBoundaryTrace rigidBoundaryTrace :
      Prop)
    (hBoundary : exactDerivative → exactSupNorm → canonicalBoundaryTrace)
    (hRigid : canonicalBoundaryTrace → rigidBoundaryTrace) :
    explicitPrimitive →
      exactDerivative →
        exactSupNorm →
          explicitPrimitive ∧ exactDerivative ∧ exactSupNorm ∧ canonicalBoundaryTrace ∧
            rigidBoundaryTrace := by
  intro hPrimitive hDerivative hNorm
  rcases
      paper_cubical_stokes_explicit_minimizer explicitPrimitive exactDerivative exactSupNorm
        canonicalBoundaryTrace rigidBoundaryTrace hBoundary hRigid hPrimitive hDerivative hNorm
    with ⟨hPrimitive', hDerivative', hNorm', hBoundaryTrace⟩
  exact ⟨hPrimitive', hDerivative', hNorm', hBoundaryTrace, hRigid hBoundaryTrace⟩

end Omega.SPG
