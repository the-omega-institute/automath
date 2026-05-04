import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-unit-circle-zero-logamplitude-holographic-rigidity`. -/
theorem paper_conclusion_unit_circle_zero_logamplitude_holographic_rigidity
    (zeroStatement fourierInversion injectiveStatement l2LowerBound : Prop)
    (hzero : zeroStatement) (hfourier : fourierInversion)
    (hinj : fourierInversion -> injectiveStatement)
    (hl2 : fourierInversion -> l2LowerBound) :
    zeroStatement /\ fourierInversion /\ injectiveStatement /\ l2LowerBound := by
  exact ⟨hzero, hfourier, hinj hfourier, hl2 hfourier⟩

end Omega.Conclusion
