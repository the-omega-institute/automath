namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the maximal collapse criterion in the
    non-focused APAL homological-visibility section.
    cor:maximal-collapse -/
theorem paper_conservative_extension_maximal_collapse
    (evaluationSurjective kernelAll visibleQuotientZero budgetMaximal : Prop)
    (hImage : evaluationSurjective ↔ kernelAll)
    (hQuot : kernelAll ↔ visibleQuotientZero)
    (hBudget : kernelAll ↔ budgetMaximal) :
    (evaluationSurjective ↔ kernelAll) ∧
      (kernelAll ↔ visibleQuotientZero) ∧
      (kernelAll ↔ budgetMaximal) ∧
      (evaluationSurjective ↔ visibleQuotientZero) := by
  exact ⟨hImage, hQuot, hBudget, hImage.trans hQuot⟩

end Omega.Topos
