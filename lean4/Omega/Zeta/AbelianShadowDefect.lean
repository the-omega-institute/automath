namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the abelian-shadow decomposition and the
    exact criterion for vanishing non-abelian defect.
    thm:abelian-shadow-defect -/
theorem paper_etds_abelian_shadow_defect
    (orthogonal factorsThroughAbelian nonabelianDefectZero higherCoefficientsZero : Prop)
    (abelianEnergy nonabelianEnergy oneDimensionalEnergy higherDimensionalEnergy : ℝ)
    (hAbEnergy : abelianEnergy = oneDimensionalEnergy)
    (hNaEnergy : nonabelianEnergy = higherDimensionalEnergy)
    (hFactorToCoeff : factorsThroughAbelian → higherCoefficientsZero)
    (hCoeffToDefect : higherCoefficientsZero → nonabelianDefectZero)
    (hDefectToFactor : nonabelianDefectZero → factorsThroughAbelian)
    (hOrthogonal : orthogonal) :
    orthogonal ∧
      abelianEnergy = oneDimensionalEnergy ∧
      nonabelianEnergy = higherDimensionalEnergy ∧
      (factorsThroughAbelian ↔ nonabelianDefectZero) ∧
      (nonabelianDefectZero ↔ higherCoefficientsZero) := by
  have hFactorToDefect : factorsThroughAbelian → nonabelianDefectZero := by
    intro hFactor
    exact hCoeffToDefect (hFactorToCoeff hFactor)
  have hDefectToCoeff : nonabelianDefectZero → higherCoefficientsZero := by
    intro hDefect
    exact hFactorToCoeff (hDefectToFactor hDefect)
  refine ⟨hOrthogonal, hAbEnergy, hNaEnergy, ?_, ?_⟩
  · exact ⟨hFactorToDefect, hDefectToFactor⟩
  · exact ⟨hDefectToCoeff, hCoeffToDefect⟩

end Omega.Zeta
