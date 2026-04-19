namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the optimal homotopy-decomposition theorem in
    `2026_cubical_stokes_inverse_boundary_readout_jdsgt`.
    thm:homotopy-decomposition -/
theorem paper_cubical_stokes_homotopy_decomposition
    (homotopyIdentity coordinateMonomialBound exactDecomposition defectDerivative optimalDefectBound
      sharpnessWitness sharpConstant : Prop)
    (hMain :
      homotopyIdentity →
        coordinateMonomialBound →
          exactDecomposition ∧ defectDerivative ∧ optimalDefectBound)
    (hSharp : sharpnessWitness → sharpConstant) :
    homotopyIdentity →
      coordinateMonomialBound →
        sharpnessWitness →
          exactDecomposition ∧ defectDerivative ∧ optimalDefectBound ∧ sharpConstant := by
  intro hIdentity hBound hWitness
  have hMain' := hMain hIdentity hBound
  exact ⟨hMain'.1, hMain'.2.1, hMain'.2.2, hSharp hWitness⟩

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the cubical homotopy decomposition with Stokes-defect control in
    `2026_cubical_stokes_inverse_boundary_readout_jdsgt`.
    thm:spg-cube-homotopy-decomposition-and-stokes-defect -/
theorem paper_spg_cube_homotopy_decomposition_and_stokes_defect
    (homotopyIdentity exactDecomposition stokesDefectBound optimalDefectConstant : Prop)
    (hMain : homotopyIdentity → exactDecomposition ∧ stokesDefectBound)
    (hOptimal : stokesDefectBound → optimalDefectConstant) :
    homotopyIdentity → exactDecomposition ∧ stokesDefectBound ∧ optimalDefectConstant := by
  intro hIdentity
  have hMain' := hMain hIdentity
  exact ⟨hMain'.1, hMain'.2, hOptimal hMain'.2⟩

end Omega.SPG
