import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-observer-two-torsion-onebit-minimal-desingularization`. -/
theorem paper_conclusion_observer_two_torsion_onebit_minimal_desingularization
    (cardR : ℕ) (pullbackBeta pullbackAlpha2 factorsThrough : Prop) (hcard : 2 ≤ cardR)
    (hcover : pullbackBeta ∧ pullbackAlpha2 ∧ factorsThrough) :
    2 ≤ cardR ∧ pullbackBeta ∧ pullbackAlpha2 ∧ factorsThrough := by
  exact ⟨hcard, hcover.1, hcover.2.1, hcover.2.2⟩

end Omega.Conclusion
