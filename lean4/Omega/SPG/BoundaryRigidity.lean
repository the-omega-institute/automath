namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the cube boundary-rigidity theorem in
    `2026_cubical_stokes_inverse_boundary_readout_jdsgt`.
    thm:boundary-rigidity -/
theorem paper_cubical_stokes_boundary_rigidity
    (hasPrimitive exactSupNorm canonicalBoundaryTrace rigidBoundaryTrace : Prop)
    (hBoundary : hasPrimitive → exactSupNorm → canonicalBoundaryTrace)
    (hRigid : canonicalBoundaryTrace → rigidBoundaryTrace) :
    hasPrimitive → exactSupNorm → canonicalBoundaryTrace ∧ rigidBoundaryTrace := by
  intro hPrimitive hNorm
  have hTrace : canonicalBoundaryTrace := hBoundary hPrimitive hNorm
  exact ⟨hTrace, hRigid hTrace⟩

end Omega.SPG
