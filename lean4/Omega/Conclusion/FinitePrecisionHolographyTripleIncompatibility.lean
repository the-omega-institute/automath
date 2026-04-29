import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-finite-precision-holography-triple-incompatibility`.
If exact recovery and uniform stability are already incompatible for a fixed-resolution boundary
holography protocol, then adding polynomial-time inversion cannot restore consistency. -/
theorem paper_conclusion_finite_precision_holography_triple_incompatibility
    (exactRecovery uniformStability polynomialTimeInversion : Prop)
    (hNoPair : ¬ (exactRecovery ∧ uniformStability)) :
    ¬ (exactRecovery ∧ uniformStability ∧ polynomialTimeInversion) := by
  intro hTriple
  exact hNoPair ⟨hTriple.1, hTriple.2.1⟩

end Omega.Conclusion
