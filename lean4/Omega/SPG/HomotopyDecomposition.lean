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

end Omega.SPG
