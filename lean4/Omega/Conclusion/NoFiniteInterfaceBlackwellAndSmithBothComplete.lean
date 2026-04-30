import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-no-finite-interface-blackwell-and-smith-both-complete`.
The fixed Smith obstruction rules out a finite interface satisfying both completeness
requirements. -/
theorem paper_conclusion_no_finite_interface_blackwell_and_smith_both_complete {Interface : Type*}
    (BlackwellMinimal SmithComplete : Interface → Prop) (T : Interface)
    (hSmithObstruction : ¬ SmithComplete T) :
    ¬ (BlackwellMinimal T ∧ SmithComplete T) := by
  intro h
  exact hSmithObstruction h.2

end Omega.Conclusion
