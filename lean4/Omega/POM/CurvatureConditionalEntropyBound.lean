import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-curvature-conditional-entropy-bound`.
The conditional entropy/Fano split and the conditional mutual-information bound compose. -/
theorem paper_pom_curvature_conditional_entropy_bound
    (curvatureTvOptimal fanoEventSplit conditionalMiBound : Prop)
    (hTv : curvatureTvOptimal)
    (hSplit : curvatureTvOptimal -> fanoEventSplit)
    (hMi : fanoEventSplit -> conditionalMiBound) :
    conditionalMiBound := by
  exact hMi (hSplit hTv)

end Omega.POM
