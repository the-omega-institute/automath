import Mathlib.Tactic

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for quantitative rigidity towards the symmetric
    two-point law.
    thm:poisson-defect-stability -/
theorem paper_circle_dimension_poisson_defect_stability
    (centeredToSign signToRademacher centeredToRademacher defectQuarterBound defectHalfBound :
      ℝ)
    (hCentered :
      centeredToSign ≤ defectHalfBound)
    (hSign :
      signToRademacher ≤ defectQuarterBound)
    (hTriangle :
      centeredToRademacher ≤ centeredToSign + signToRademacher) :
    centeredToRademacher ≤ defectQuarterBound + defectHalfBound := by
  linarith

set_option maxHeartbeats 400000 in
/-- Lower-case publication theorem matching the round target name.
    thm:poisson-defect-stability -/
theorem paper_poisson_defect_stability
    (centeredToSign signToRademacher centeredToRademacher defectQuarterBound defectHalfBound :
      ℝ)
    (hCentered :
      centeredToSign ≤ defectHalfBound)
    (hSign :
      signToRademacher ≤ defectQuarterBound)
    (hTriangle :
      centeredToRademacher ≤ centeredToSign + signToRademacher) :
    centeredToRademacher ≤ defectQuarterBound + defectHalfBound := by
  exact
    paper_circle_dimension_poisson_defect_stability centeredToSign signToRademacher
      centeredToRademacher defectQuarterBound defectHalfBound hCentered hSign hTriangle

end Omega.CircleDimension
