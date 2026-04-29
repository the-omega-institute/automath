import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-boundary-superselection-sideinfo-cost-lower-bound`. -/
theorem paper_conclusion_window6_boundary_superselection_sideinfo_cost_lower_bound
    (r dimR : ℕ) (h : 64 ≤ 21 + r + dimR) :
    43 ≤ r + dimR ∧ (r = 3 → 40 ≤ dimR) ∧ (r = 1 → 42 ≤ dimR) := by
  omega

end Omega.Conclusion
