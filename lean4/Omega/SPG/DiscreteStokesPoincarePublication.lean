namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the cubical Stokes--Poincare theorem in
    `2026_cubical_stokes_inverse_boundary_readout_jdsgt`.
    thm:discrete-stokes-poincare -/
theorem paper_cubical_stokes_discrete_stokes_poincare
    (hasWhitneyCoordinateMonomialCoboundary exactDecomposition defectControlled sharpConstant :
      Prop)
    (hDecomp : hasWhitneyCoordinateMonomialCoboundary → exactDecomposition)
    (hDefect : exactDecomposition → defectControlled)
    (hSharp : hasWhitneyCoordinateMonomialCoboundary → sharpConstant) :
    hasWhitneyCoordinateMonomialCoboundary →
      exactDecomposition ∧ defectControlled ∧ sharpConstant := by
  intro hCoboundary
  have hExact : exactDecomposition := hDecomp hCoboundary
  exact ⟨hExact, hDefect hExact, hSharp hCoboundary⟩

end Omega.SPG
