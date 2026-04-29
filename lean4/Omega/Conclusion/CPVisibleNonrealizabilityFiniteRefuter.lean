import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-cp-visible-nonrealizability-has-finite-refuter`. -/
theorem paper_conclusion_cp_visible_nonrealizability_has_finite_refuter {Channel : Type*}
    (cpVisible : Prop) (toeplitzFails : Channel → Nat → Prop)
    (h : cpVisible ↔ ∀ π N, ¬ toeplitzFails π N) :
    ¬ cpVisible → ∃ π N, toeplitzFails π N := by
  intro h_not_cp
  by_contra h_no_refuter
  apply h_not_cp
  exact h.mpr (fun π N hfail => h_no_refuter ⟨π, N, hfail⟩)

end Omega.Conclusion
