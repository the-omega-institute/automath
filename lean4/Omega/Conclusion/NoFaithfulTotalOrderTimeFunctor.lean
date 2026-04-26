import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-no-faithful-total-order-time-functor`. A faithful total-order
time functor would force a global clock, contradicting the nontrivial Čech-`H^2` obstruction. -/
theorem paper_conclusion_no_faithful_total_order_time_functor
    {O T Obstruction Clock : Type*} [Preorder T] (hasNontrivialH2 : Obstruction → Prop)
    (faithfulTotalOrderTimeFunctor : (O → T) → Prop) (globalClock : Clock → Prop)
    (forcesClock :
      ∀ F : O → T, faithfulTotalOrderTimeFunctor F → ∃ tau : Clock, globalClock tau)
    (noClock :
      ∀ omega : Obstruction, hasNontrivialH2 omega → ¬ ∃ tau : Clock, globalClock tau)
    (omega : Obstruction) (homega : hasNontrivialH2 omega) :
    ¬ ∃ F : O → T, faithfulTotalOrderTimeFunctor F := by
  rintro ⟨F, hF⟩
  exact noClock omega homega (forcesClock F hF)

end Omega.Conclusion
