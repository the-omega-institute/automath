import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-singular-ring-unit-circle-maximal-shell`. The unit-circle
negative-ray confinement together with the off-circle sign crossing yield the maximal-shell
conclusion. -/
theorem paper_conclusion_singular_ring_unit_circle_maximal_shell
    (unitCircleNegativeRay offCircleSignCrossing maximalShell : Prop)
    (hUnit : unitCircleNegativeRay)
    (hOff : offCircleSignCrossing)
    (hMax : unitCircleNegativeRay -> offCircleSignCrossing -> maximalShell) :
    unitCircleNegativeRay ∧ offCircleSignCrossing ∧ maximalShell := by
  exact ⟨hUnit, hOff, hMax hUnit hOff⟩

end Omega.Conclusion
