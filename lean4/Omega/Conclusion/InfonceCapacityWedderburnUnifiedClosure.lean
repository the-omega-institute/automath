import Omega.Conclusion.CapacityOrderedSpectrumInfoNCEEquivalence
import Omega.Zeta.ConclusionWedderburnThresholdHolography

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-infonce-capacity-wedderburn-unified-closure`. -/
theorem paper_conclusion_infonce_capacity_wedderburn_unified_closure
    (D : Omega.Zeta.conclusion_wedderburn_threshold_holography_data) :
    Omega.Conclusion.conclusion_capacity_ordered_spectrum_infonce_equivalence_statement ∧
      D.capacityCurveDeterminesTailCounts ∧
      D.tailCountsDetermineHistogram ∧
      D.histogramDeterminesWedderburnClass := by
  have hWedderburn := Omega.Zeta.paper_conclusion_wedderburn_threshold_holography D
  exact ⟨paper_conclusion_capacity_ordered_spectrum_infonce_equivalence,
    hWedderburn.1, hWedderburn.2.1, hWedderburn.2.2⟩

end Omega.Conclusion
