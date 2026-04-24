import Mathlib.Tactic
import Omega.Conclusion.DoubleSignCylinderTrigonalTransparency

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-double-sign-trigonal-zero-mutual-information`. Once the sign-box
transparency statement is known, the vanishing of the mutual information and the centered
orthogonality consequence are immediate corollaries. -/
theorem paper_conclusion_double_sign_trigonal_zero_mutual_information
    (signBoxTransparency mutualInformationZero centeredObservableOrthogonality : Prop)
    (hTransparency : signBoxTransparency)
    (hMutual : signBoxTransparency -> mutualInformationZero)
    (hOrth : signBoxTransparency -> centeredObservableOrthogonality) :
    signBoxTransparency ∧ mutualInformationZero ∧ centeredObservableOrthogonality := by
  exact ⟨hTransparency, hMutual hTransparency, hOrth hTransparency⟩

end Omega.Conclusion
