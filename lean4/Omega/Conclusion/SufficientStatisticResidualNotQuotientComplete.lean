import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-sufficient-statistic-residual-not-quotient-complete`. -/
theorem paper_conclusion_sufficient_statistic_residual_not_quotient_complete
    (d nu : ℕ) (residualImageBound quotientCountBound quotientIncomplete : Prop)
    (hbound : residualImageBound)
    (hcount : residualImageBound → quotientCountBound)
    (hincomplete : nu + 1 < d → quotientCountBound → quotientIncomplete)
    (hlarge : nu + 1 < d) :
    quotientCountBound ∧ quotientIncomplete := by
  have hquotientCount : quotientCountBound := hcount hbound
  exact ⟨hquotientCount, hincomplete hlarge hquotientCount⟩

end Omega.Conclusion
