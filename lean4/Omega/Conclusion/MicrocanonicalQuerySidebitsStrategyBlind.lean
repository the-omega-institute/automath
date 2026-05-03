import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper-facing wrapper for the side-bit strategy-blind recovery package.
    thm:conclusion-microcanonical-query-sidebits-strategy-blind -/
theorem paper_conclusion_microcanonical_query_sidebits_strategy_blind
    (posteriorClosedForm strategyIndependence gaussianWindow : Prop) (hClosed : posteriorClosedForm)
    (hInd : posteriorClosedForm → strategyIndependence)
    (hGauss : strategyIndependence → gaussianWindow) :
    posteriorClosedForm ∧ strategyIndependence ∧ gaussianWindow := by
  exact ⟨hClosed, hInd hClosed, hGauss (hInd hClosed)⟩

end Omega.Conclusion
