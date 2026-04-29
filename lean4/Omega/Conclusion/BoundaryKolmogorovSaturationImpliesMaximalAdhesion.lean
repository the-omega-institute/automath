import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label:
`cor:conclusion-boundary-kolmogorov-saturation-implies-maximal-adhesion`. -/
theorem paper_conclusion_boundary_kolmogorov_saturation_implies_maximal_adhesion
    (kolmogorovSaturation boundaryGodelSaturation phaseDiagram maximalAdhesion : Prop)
    (hSat : kolmogorovSaturation)
    (hBoundary : kolmogorovSaturation -> boundaryGodelSaturation)
    (hPhase : boundaryGodelSaturation -> phaseDiagram)
    (hMax : phaseDiagram -> maximalAdhesion) :
    boundaryGodelSaturation ∧ phaseDiagram ∧ maximalAdhesion := by
  exact ⟨hBoundary hSat, hPhase (hBoundary hSat), hMax (hPhase (hBoundary hSat))⟩

end Omega.Conclusion
