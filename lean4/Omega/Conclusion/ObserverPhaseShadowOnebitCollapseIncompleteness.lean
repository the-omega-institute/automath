import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-observer-phase-shadow-onebit-collapse-incompleteness`. -/
theorem paper_conclusion_observer_phase_shadow_onebit_collapse_incompleteness
    (betaNonzero alpha2Nonzero negativeLoop alphaNonzero globalReadable : Prop)
    (hcollapse₁ : betaNonzero ↔ alpha2Nonzero)
    (hcollapse₂ : alpha2Nonzero ↔ negativeLoop)
    (hblind : alphaNonzero → ¬ alpha2Nonzero → ¬ globalReadable) :
    ((betaNonzero ↔ alpha2Nonzero) ∧ (alpha2Nonzero ↔ negativeLoop)) ∧
      (alphaNonzero → ¬ alpha2Nonzero → ¬ globalReadable) := by
  exact ⟨⟨hcollapse₁, hcollapse₂⟩, hblind⟩

end Omega.Conclusion
