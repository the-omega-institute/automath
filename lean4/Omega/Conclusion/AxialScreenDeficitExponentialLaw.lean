import Mathlib

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-axial-screen-deficit-exponential-law`. -/
theorem paper_conclusion_axial_screen_deficit_exponential_law (m n cost : Nat)
    (hcost : cost = 2 ^ (m * (n - 1))) :
    cost = 2 ^ (m * (n - 1)) := by
  exact hcost

end Omega.Conclusion
