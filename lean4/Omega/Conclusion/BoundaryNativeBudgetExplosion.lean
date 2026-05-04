import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-boundary-native-budget-explosion`.
The native Pareto frontier bound immediately yields the two bounded-register and bounded-phase
subtraction corollaries. -/
theorem paper_conclusion_boundary_native_budget_explosion (r alphaReg d D A : ℕ)
    (hfrontier : r ≤ alphaReg + d) (hd : d ≤ D) (ha : alphaReg ≤ A) :
    r ≤ alphaReg + d ∧ r - D ≤ alphaReg ∧ r - A ≤ d := by
  constructor
  · exact hfrontier
  constructor
  · omega
  · omega

end Omega.Conclusion
