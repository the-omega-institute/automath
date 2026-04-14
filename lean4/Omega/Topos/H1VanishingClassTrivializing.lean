namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the `H_1`-vanishing class-trivializing corollary.
    cor:h1-vanishing-class-trivializing -/
theorem paper_gluing_failure_h1_vanishing_class_trivializing
    (H1Zero qωZero pureExt factorizes : Prop)
    (hExt : H1Zero → (qωZero ↔ pureExt))
    (hInitial : pureExt ↔ factorizes) :
    H1Zero → (qωZero ↔ factorizes) := by
  intro hH1
  exact (hExt hH1).trans hInitial

end Omega.Topos
