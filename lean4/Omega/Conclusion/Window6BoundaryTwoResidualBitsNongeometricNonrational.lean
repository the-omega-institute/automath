import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper-facing wrapper for the residual two-bit nongeometric and nonrational conclusion.
    cor:conclusion-window6-boundary-two-residual-bits-nongeometric-nonrational -/
theorem paper_conclusion_window6_boundary_two_residual_bits_nongeometric_nonrational
    (zeroOneThreeLaw residualQuotient twoBitsNongeometric twoBitsNonrational : Prop)
    (hLaw : zeroOneThreeLaw) (hQuot : zeroOneThreeLaw → residualQuotient)
    (hGeo : residualQuotient → twoBitsNongeometric)
    (hRat : residualQuotient → twoBitsNonrational) :
    residualQuotient ∧ twoBitsNongeometric ∧ twoBitsNonrational := by
  exact ⟨hQuot hLaw, hGeo (hQuot hLaw), hRat (hQuot hLaw)⟩

end Omega.Conclusion
