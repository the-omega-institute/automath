import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-turing-completeness-obstructs-eventual-omega-vanishing`. -/
theorem paper_conclusion_turing_completeness_obstructs_eventual_omega_vanishing
    (eventualOmegaZero effectiveLift computableH2 semanticGaugeCoincidence
      semanticEqDecidable turingCompleteUndecidable : Prop)
    (hdecision : eventualOmegaZero -> effectiveLift -> computableH2 ->
      semanticGaugeCoincidence -> semanticEqDecidable)
    (hundecidable : turingCompleteUndecidable -> Not semanticEqDecidable) :
    turingCompleteUndecidable ->
      Not (eventualOmegaZero ∧ effectiveLift ∧ computableH2 ∧ semanticGaugeCoincidence) := by
  intro hturing hpack
  rcases hpack with ⟨hzero, hlift, hH2, hgauge⟩
  exact hundecidable hturing (hdecision hzero hlift hH2 hgauge)

end Omega.Conclusion
