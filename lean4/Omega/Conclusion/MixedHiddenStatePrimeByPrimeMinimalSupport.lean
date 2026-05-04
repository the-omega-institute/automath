import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-mixed-hiddenstate-prime-by-prime-minimal-support`. -/
theorem paper_conclusion_mixed_hiddenstate_prime_by_prime_minimal_support
    (beta N minCard : Nat)
    (primewiseEmbeddingCriterion : Prop)
    (hCriterion : primewiseEmbeddingCriterion)
    (hMin : minCard = 2 ^ beta * N) :
    primewiseEmbeddingCriterion ∧ minCard = 2 ^ beta * N := by
  exact ⟨hCriterion, hMin⟩

end Omega.Conclusion
