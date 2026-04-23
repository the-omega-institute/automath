import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-anomaly-hodge-onepoint-criterion`. -/
theorem paper_conclusion_anomaly_hodge_onepoint_criterion
    (zeroClass onePointZero discreteInvariantZero : Prop) (h12 : zeroClass ↔ onePointZero)
    (h13 : zeroClass ↔ discreteInvariantZero) :
    zeroClass ↔ (onePointZero ∧ discreteInvariantZero) := by
  constructor
  · intro hzero
    exact ⟨h12.mp hzero, h13.mp hzero⟩
  · intro hpair
    exact h12.mpr hpair.1

end Omega.Conclusion
