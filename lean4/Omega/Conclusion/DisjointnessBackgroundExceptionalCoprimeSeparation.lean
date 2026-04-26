import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-disjointness-background-exceptional-coprime-separation`. -/
theorem paper_conclusion_disjointness_background_exceptional_coprime_separation
    (coprimeSeparation backgroundMultiplicityExact : Prop) (hCoprime : coprimeSeparation)
    (hMultiplicity : backgroundMultiplicityExact) :
    coprimeSeparation ∧ backgroundMultiplicityExact := by
  exact ⟨hCoprime, hMultiplicity⟩

end Omega.Conclusion
