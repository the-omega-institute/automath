import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-so10-center-deficit`. -/
theorem paper_conclusion_window6_so10_center_deficit
    (centerTwoRank fullBoundaryParityRank protocolCokernelRank : Nat)
    (hcenter : centerTwoRank <= 1) (hfull : fullBoundaryParityRank = 3)
    (hprotocol : protocolCokernelRank = 2) :
    centerTwoRank <= 1 ∧ centerTwoRank < fullBoundaryParityRank ∧
      centerTwoRank < protocolCokernelRank := by
  omega

end Omega.Conclusion
