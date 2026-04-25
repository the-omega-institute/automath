import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-finite-unit-gluing-stokes-invisibility`. If both Stokes width and
unit-visibility defects are the negative integer cast of the unit free rank, then their vanishing
is equivalent, and both vanish exactly when the free rank is zero. -/
theorem paper_conclusion_finite_unit_gluing_stokes_invisibility
    (unitFreeRank : Nat) (wdimGap uVisGap : Int)
    (hW : wdimGap = -((unitFreeRank : Int)))
    (hU : uVisGap = -((unitFreeRank : Int))) :
    (wdimGap = 0 ↔ uVisGap = 0) ∧ (wdimGap = 0 ↔ unitFreeRank = 0) := by
  subst wdimGap
  subst uVisGap
  constructor
  · simp
  · constructor
    · intro h
      have hcast : (unitFreeRank : Int) = 0 := by
        linarith
      exact Int.ofNat_eq_zero.mp hcast
    · intro h
      simp [h]

end Omega.Conclusion
