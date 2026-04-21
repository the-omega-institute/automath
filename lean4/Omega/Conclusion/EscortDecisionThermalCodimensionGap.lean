import Mathlib.Tactic

namespace Omega.Conclusion

/-- Packaging the fixed-sample escort-collapse decision codimension `1` with the ordered-spectrum
InfoNCE recovery codimension `|X| - 1` leaves a gap of `|X| - 2`.
    thm:conclusion-escort-decision-thermal-codimension-gap -/
theorem paper_conclusion_escort_decision_thermal_codimension_gap {X : Type} [Fintype X]
    (decisionDim recoveryDim : Nat) (hDecision : decisionDim = 1)
    (hRecovery : recoveryDim = Fintype.card X - 1) :
    recoveryDim - decisionDim = Fintype.card X - 2 := by
  subst decisionDim
  subst recoveryDim
  omega

end Omega.Conclusion
