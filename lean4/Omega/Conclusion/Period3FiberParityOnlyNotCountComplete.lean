import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-period3-fiber-parity-only-not-count-complete`. -/
theorem paper_conclusion_period3_fiber_parity_only_not_count_complete
    (n : Nat)
    (SharpPComplete ParsimoniousReduction TwoParityClasses CountCompleteFailure : Prop)
    (hsharp : SharpPComplete) (hpars : ParsimoniousReduction) (htwo : TwoParityClasses)
    (hfail : SharpPComplete -> ParsimoniousReduction -> TwoParityClasses ->
      CountCompleteFailure) :
    SharpPComplete ∧ ParsimoniousReduction ∧ TwoParityClasses ∧ CountCompleteFailure := by
  cases n
  exact ⟨hsharp, hpars, htwo, hfail hsharp hpars htwo⟩
  exact ⟨hsharp, hpars, htwo, hfail hsharp hpars htwo⟩

end Omega.Conclusion
