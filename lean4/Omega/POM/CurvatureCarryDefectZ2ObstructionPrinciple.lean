import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-curvature-carry-defect-z2-obstruction-principle`. -/
theorem paper_pom_curvature_carry_defect_z2_obstruction_principle
    (curvatureStokes carryValuation z2Obstruction : Prop)
    (hCurvature : curvatureStokes → z2Obstruction)
    (hCarry : carryValuation → z2Obstruction)
    (hRealize : z2Obstruction → curvatureStokes ∧ carryValuation) :
    curvatureStokes ↔ carryValuation := by
  constructor
  · intro h
    exact (hRealize (hCurvature h)).2
  · intro h
    exact (hRealize (hCarry h)).1

end Omega.POM
