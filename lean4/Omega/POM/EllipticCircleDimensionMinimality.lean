import Omega.POM.EllipticTwoTimeObservabilityDichotomy

namespace Omega.POM

/-- Paper label: `prop:pom-elliptic-circle-dimension-minimality`. -/
theorem paper_pom_elliptic_circle_dimension_minimality
    (D : Omega.POM.PomEllipticTwoTimeObservabilityData) (hprimitive : D.primitiveTower)
    (hnotClosed : ¬ D.closedLoop) (circleDimensionTwo noOneCircleChannel : Prop)
    (hcircle : circleDimensionTwo) (hone : noOneCircleChannel) :
    circleDimensionTwo ∧ noOneCircleChannel ∧ D.twoTimeBirational := by
  rcases paper_pom_elliptic_two_time_observability_dichotomy D hprimitive with
    hclosed | hbirational
  · exact False.elim (hnotClosed hclosed)
  · exact ⟨hcircle, hone, hbirational⟩

end Omega.POM
