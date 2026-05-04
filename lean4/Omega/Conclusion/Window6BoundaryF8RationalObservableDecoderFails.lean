import Omega.Conclusion.Window6BoundaryF8RationalGeneratedAlgebraBlind

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-boundary-f8-rational-observable-decoder-fails`. -/
theorem paper_conclusion_window6_boundary_f8_rational_observable_decoder_fails {B G : Type*}
    [Group G] [MulAction G B] (S : Set (B → Complex))
    (hS : ∀ f, f ∈ S → ∀ (g : G) (x : B), f (g • x) = f x) :
    ∀ f, f ∈ Algebra.adjoin Complex S → ∀ (g : G) (x : B), f (g • x) = f x := by
  exact paper_conclusion_window6_boundary_f8_rational_generated_algebra_blind S hS

end Omega.Conclusion
