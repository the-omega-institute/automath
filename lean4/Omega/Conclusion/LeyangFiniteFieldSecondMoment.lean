import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-leyang-finite-field-second-moment`.
The counting identity is assembled from diagonal and off-diagonal contributions, then passed
through the Weil-bound input to the stated asymptotic mean. -/
theorem paper_conclusion_leyang_finite_field_second_moment
    (secondMomentIdentity diagonalContribution offDiagonalContribution weilErrorBound
      asymptoticMean : Prop)
    (hIdentity : diagonalContribution -> offDiagonalContribution -> secondMomentIdentity)
    (hDiag : diagonalContribution)
    (hOffDiag : offDiagonalContribution)
    (hWeil : secondMomentIdentity -> weilErrorBound)
    (hAsymptotic : weilErrorBound -> asymptoticMean) :
    secondMomentIdentity ∧ weilErrorBound ∧ asymptoticMean := by
  have hSecondMoment : secondMomentIdentity := hIdentity hDiag hOffDiag
  exact ⟨hSecondMoment, hWeil hSecondMoment, hAsymptotic (hWeil hSecondMoment)⟩

end Omega.Conclusion
