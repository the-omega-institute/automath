import Omega.SPG.BoundaryRigidity

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the explicit-minimizer corollary in
    `2026_cubical_stokes_inverse_boundary_readout_jdsgt`.
    cor:explicit-minimizer -/
theorem paper_cubical_stokes_explicit_minimizer
    (explicitFormula exactDerivative exactSupNorm canonicalBoundaryTrace rigidBoundaryTrace : Prop)
    (hBoundary : exactDerivative → exactSupNorm → canonicalBoundaryTrace)
    (hRigid : canonicalBoundaryTrace → rigidBoundaryTrace) :
    explicitFormula →
      exactDerivative →
        exactSupNorm →
          explicitFormula ∧ exactDerivative ∧ exactSupNorm ∧ canonicalBoundaryTrace := by
  intro hFormula hDerivative hNorm
  have hBoundaryRigidity :=
    paper_cubical_stokes_boundary_rigidity
      exactDerivative exactSupNorm canonicalBoundaryTrace rigidBoundaryTrace hBoundary hRigid
      hDerivative hNorm
  exact ⟨hFormula, hDerivative, hNorm, hBoundaryRigidity.1⟩

end Omega.SPG
