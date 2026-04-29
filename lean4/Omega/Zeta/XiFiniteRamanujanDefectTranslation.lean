import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-finite-ramanujan-defect-translation`. -/
theorem paper_xi_finite_ramanujan_defect_translation
    (unitCircleCriterion jensenDefectZero ramanujanPhaseClosure : Prop)
    (hUnitJensen : unitCircleCriterion ↔ jensenDefectZero)
    (hJensenRamanujan : jensenDefectZero ↔ ramanujanPhaseClosure) :
    unitCircleCriterion ↔ ramanujanPhaseClosure := by
  exact hUnitJensen.trans hJensenRamanujan

end Omega.Zeta
