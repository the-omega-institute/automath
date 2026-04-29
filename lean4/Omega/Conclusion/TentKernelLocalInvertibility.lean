import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete single-cell data for the two adjacent tent-kernel weights and their zeroth/first
moment identities. -/
structure ConclusionCellCurvatureTwoMomentData where
  cellIndex : ℚ
  wLeft : ℚ
  wRight : ℚ
  leftTentMoment : ℚ
  rightTentMoment : ℚ
  totalMass : ℚ
  firstMoment : ℚ
  hLeft : wLeft = leftTentMoment
  hRight : wRight = rightTentMoment
  hMass : wLeft + wRight = totalMass
  hFirstMoment : cellIndex * wLeft + (cellIndex + 1) * wRight = firstMoment

/-- Paper wrapper for the two-moment completeness of adjacent cell tent kernels.
    thm:conclusion-cell-curvature-two-moment-completeness -/
theorem paper_conclusion_cell_curvature_two_moment_completeness
    (D : ConclusionCellCurvatureTwoMomentData) :
    D.wLeft = D.leftTentMoment ∧ D.wRight = D.rightTentMoment ∧
      D.wLeft + D.wRight = D.totalMass ∧
      D.cellIndex * D.wLeft + (D.cellIndex + 1) * D.wRight = D.firstMoment := by
  exact ⟨D.hLeft, D.hRight, D.hMass, D.hFirstMoment⟩

/-- Paper label: `cor:conclusion-cell-curvature-barycenter-adjacent-peak-ratio`. -/
theorem paper_conclusion_cell_curvature_barycenter_adjacent_peak_ratio
    (D : ConclusionCellCurvatureTwoMomentData) (hpos : D.totalMass ≠ 0) :
    D.firstMoment / D.totalMass = D.cellIndex + D.wRight / (D.wLeft + D.wRight) := by
  have hden : D.wLeft + D.wRight ≠ 0 := by
    intro hzero
    exact hpos (by rw [← D.hMass, hzero])
  rw [← D.hMass, ← D.hFirstMoment]
  field_simp [hden]
  ring

end Omega.Conclusion
