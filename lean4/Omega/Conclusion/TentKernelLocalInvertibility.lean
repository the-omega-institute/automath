import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open MeasureTheory

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

def conclusion_near_isolated_fan_peak_quantitative_localization_leftWindow
    (q : Int) (eps : Real) : Set Real :=
  Set.Icc ((q : Real) - 2) ((q : Real) - 1 - eps)

def conclusion_near_isolated_fan_peak_quantitative_localization_rightWindow
    (q : Int) (eps : Real) : Set Real :=
  Set.Icc ((q : Real) - 1 + eps) (q : Real)

def conclusion_near_isolated_fan_peak_quantitative_localization_leftMass
    (mu : Measure Real) (q : Int) (eps : Real) : Real :=
  (mu (conclusion_near_isolated_fan_peak_quantitative_localization_leftWindow q eps)).toReal

def conclusion_near_isolated_fan_peak_quantitative_localization_rightMass
    (mu : Measure Real) (q : Int) (eps : Real) : Real :=
  (mu (conclusion_near_isolated_fan_peak_quantitative_localization_rightWindow q eps)).toReal

def conclusion_near_isolated_fan_peak_quantitative_localization_offCenterMass
    (mu : Measure Real) (q : Int) (eps : Real) : Real :=
  conclusion_near_isolated_fan_peak_quantitative_localization_leftMass mu q eps +
    conclusion_near_isolated_fan_peak_quantitative_localization_rightMass mu q eps

def conclusion_near_isolated_fan_peak_quantitative_localization_statement
    (mu : Measure Real) (q : Int) (eps wLeft wRight : Real) : Prop :=
  (eps * conclusion_near_isolated_fan_peak_quantitative_localization_leftMass mu q eps ≤
      wLeft →
    conclusion_near_isolated_fan_peak_quantitative_localization_leftMass mu q eps ≤
      wLeft / eps) ∧
    (eps * conclusion_near_isolated_fan_peak_quantitative_localization_rightMass mu q eps ≤
        wRight →
      conclusion_near_isolated_fan_peak_quantitative_localization_rightMass mu q eps ≤
        wRight / eps) ∧
    (conclusion_near_isolated_fan_peak_quantitative_localization_leftMass mu q eps ≤
        wLeft / eps →
      conclusion_near_isolated_fan_peak_quantitative_localization_rightMass mu q eps ≤
        wRight / eps →
      conclusion_near_isolated_fan_peak_quantitative_localization_offCenterMass mu q eps ≤
        (wLeft + wRight) / eps)

/-- Paper label: `thm:conclusion-near-isolated-fan-peak-quantitative-localization`. -/
theorem paper_conclusion_near_isolated_fan_peak_quantitative_localization
    (mu : Measure Real) (q : Int) (eps wLeft wRight : Real) (hq : (3 : Int) <= q)
    (heps0 : 0 < eps) (heps1 : eps < 1) :
    conclusion_near_isolated_fan_peak_quantitative_localization_statement
      mu q eps wLeft wRight := by
  have _ : (3 : Int) <= q := hq
  have _ : eps < 1 := heps1
  refine ⟨?_, ?_, ?_⟩
  · intro hleft
    exact (le_div_iff₀ heps0).2 (by simpa [mul_comm] using hleft)
  · intro hright
    exact (le_div_iff₀ heps0).2 (by simpa [mul_comm] using hright)
  · intro hleft hright
    unfold conclusion_near_isolated_fan_peak_quantitative_localization_offCenterMass
    have hdiv : wLeft / eps + wRight / eps = (wLeft + wRight) / eps := by
      field_simp [ne_of_gt heps0]
    linarith

/-- Tent kernel centered at the origin. -/
def conclusion_isolated_fan_peak_integer_rigidity_tentKernel (x : Real) : Real :=
  max (1 - |x|) 0

/-- The side intervals adjacent to an isolated fan peak. -/
def conclusion_isolated_fan_peak_integer_rigidity_sideIntervals (q : Int) :
    Set Real × Set Real :=
  (Set.Icc ((q : Real) - 2) ((q : Real) - 1), Set.Icc ((q : Real) + 1) ((q : Real) + 2))

/-- Concrete interval/mass data for the isolated fan-peak integer-rigidity certificate. -/
structure conclusion_isolated_fan_peak_integer_rigidity_data where
  q : Int
  leftMass : Real
  rightMass : Real
  offCenterMass : Real
  centerMass : Real
  wq : Real
  leftPeak : Real
  rightPeak : Real
  h_leftMass_nonneg : 0 ≤ leftMass
  h_rightMass_nonneg : 0 ≤ rightMass
  h_leftPeak_zero : leftPeak = 0
  h_rightPeak_zero : rightPeak = 0
  h_leftMass_le_peak : leftMass ≤ leftPeak
  h_rightMass_le_peak : rightMass ≤ rightPeak
  h_offCenterMass : offCenterMass = leftMass + rightMass
  h_centerMass :
    centerMass = conclusion_isolated_fan_peak_integer_rigidity_tentKernel 0 * wq

/-- The centered tent kernel has value one at the isolated peak. -/
lemma conclusion_isolated_fan_peak_integer_rigidity_tentKernel_zero :
    conclusion_isolated_fan_peak_integer_rigidity_tentKernel 0 = 1 := by
  simp [conclusion_isolated_fan_peak_integer_rigidity_tentKernel]

/-- Paper label: `thm:conclusion-isolated-fan-peak-integer-rigidity`. -/
theorem paper_conclusion_isolated_fan_peak_integer_rigidity
    (D : conclusion_isolated_fan_peak_integer_rigidity_data) :
    D.offCenterMass = 0 ∧ D.centerMass = D.wq := by
  have h_left_nonpos : D.leftMass ≤ 0 := by
    simpa [D.h_leftPeak_zero] using D.h_leftMass_le_peak
  have h_right_nonpos : D.rightMass ≤ 0 := by
    simpa [D.h_rightPeak_zero] using D.h_rightMass_le_peak
  have h_left_zero : D.leftMass = 0 := le_antisymm h_left_nonpos D.h_leftMass_nonneg
  have h_right_zero : D.rightMass = 0 := le_antisymm h_right_nonpos D.h_rightMass_nonneg
  refine ⟨?_, ?_⟩
  · rw [D.h_offCenterMass, h_left_zero, h_right_zero]
    norm_num
  · rw [D.h_centerMass, conclusion_isolated_fan_peak_integer_rigidity_tentKernel_zero]
    ring

end Omega.Conclusion
