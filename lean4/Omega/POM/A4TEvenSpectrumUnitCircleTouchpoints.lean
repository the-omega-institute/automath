import Mathlib.Tactic
import Omega.POM.A4tUnitCircleSpectrumClassification

namespace Omega.POM

/-- The even-spectrum unit-zero predicate, represented by the classified A4(t) unit-circle
touchpoint parameters.

Paper label: `cor:pom-a4t-even-spectrum-unit-circle-touchpoints`. -/
def pom_a4t_even_spectrum_unit_circle_touchpoints_hasUnitZero (t : ℚ) : Prop :=
  t ∈ a4tUnitCircleTouchParameters

/-- The even-spectrum unit-circle touchpoints occur exactly at the three classified parameters.

Paper label: `cor:pom-a4t-even-spectrum-unit-circle-touchpoints`. -/
theorem paper_pom_a4t_even_spectrum_unit_circle_touchpoints (t : ℚ) :
    pom_a4t_even_spectrum_unit_circle_touchpoints_hasUnitZero t ↔
      t = (-11 : ℚ) / 4 ∨ t = -1 ∨ t = 1 := by
  have hparams :
      a4tUnitCircleTouchParameters = ({(-11 : ℚ) / 4, -1, 1} : Finset ℚ) :=
    paper_pom_a4t_unit_circle_spectrum_classification.2.1
  simp [pom_a4t_even_spectrum_unit_circle_touchpoints_hasUnitZero, hparams]

end Omega.POM
