import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-discrete-chernoff-fan-strictly-sandwiched-by-continuous-legendre`. -/
theorem paper_conclusion_discrete_chernoff_fan_strictly_sandwiched_by_continuous_legendre
    (secantEqualsDiscrete legendreInequality equalityCase strictCase : Prop)
    (hSecant : secantEqualsDiscrete) (hLe : secantEqualsDiscrete -> legendreInequality)
    (hEq : legendreInequality -> equalityCase) (hStrict : legendreInequality -> strictCase) :
    And secantEqualsDiscrete (And legendreInequality (And equalityCase strictCase)) := by
  exact ⟨hSecant, hLe hSecant, hEq (hLe hSecant), hStrict (hLe hSecant)⟩

end Omega.Conclusion
