import Mathlib.Tactic

namespace Omega.Conclusion

/-- The Euler-factor split and trace additivity imply the corresponding point-count identity.
    cor:conclusion-c6-euler-factor-pointcount -/
theorem paper_conclusion_c6_euler_factor_pointcount {A : Type*} [Semiring A] (LpC6 LpC LpR : A)
    (q trC6 trC trR pointsC6 pointsC pointsR : Int) (hL : LpC6 = LpC * LpR ^ 2)
    (hTrace : trC6 = trC + 2 * trR) (hC6 : pointsC6 = q + 1 - trC6)
    (hC : pointsC = q + 1 - trC) (hR : pointsR = q + 1 - trR) :
    LpC6 = LpC * LpR ^ 2 ∧ pointsC6 = pointsC + 2 * pointsR - 2 * (q + 1) := by
  constructor
  · exact hL
  · omega

end Omega.Conclusion
