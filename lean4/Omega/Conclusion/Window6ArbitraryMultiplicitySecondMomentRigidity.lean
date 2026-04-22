import Mathlib.Tactic

namespace Omega.Conclusion

/-- The explicit diagonal second-moment tensor for window-6 cyclic multiplicity weights is
scalar exactly when the three shell weights coincide.
    thm:conclusion-window6-arbitrary-multiplicity-second-moment-rigidity -/
theorem paper_conclusion_window6_arbitrary_multiplicity_second_moment_rigidity
    (f2 f3 f4 : ℤ) :
    let d1 := f2 + 4 * f3 + 5 * f4
    let d2 := 4 * f2 + 6 * f4
    let d3 := 4 * f2 + 4 * f3 + 2 * f4
    (d1 = d2 ∧ d2 = d3) ↔ (f2 = f3 ∧ f3 = f4) := by
  dsimp
  omega

end Omega.Conclusion
