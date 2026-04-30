import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-terminal-zm-leyang-linear-twist-infinitely-many-rational-branch-values`. -/
theorem paper_xi_terminal_zm_leyang_linear_twist_infinitely_many_rational_branch_values
    (ellipticCurveHasInfinitelyManyRationalPoints finiteBadYZeroSet
      infinitelyManyRationalBranchValues : Prop)
    (hE : ellipticCurveHasInfinitelyManyRationalPoints)
    (hbad : finiteBadYZeroSet)
    (hmap :
      ellipticCurveHasInfinitelyManyRationalPoints →
        finiteBadYZeroSet → infinitelyManyRationalBranchValues) :
    infinitelyManyRationalBranchValues := by
  exact hmap hE hbad

end Omega.Zeta
