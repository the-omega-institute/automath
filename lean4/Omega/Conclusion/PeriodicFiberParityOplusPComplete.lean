import Mathlib.Tactic

namespace Omega.Conclusion

/-- The parity decision predicate attached to a finite accepting set. -/
def conclusion_periodic_fiber_parity_oplusp_complete_parity_decision {α : Type*}
    [Fintype α] [DecidableEq α] (accepts : α → Bool) : Prop :=
  Odd ((Finset.univ.filter fun x => accepts x).card)

/-- Paper label: `thm:conclusion-periodic-fiber-parity-oplusP-complete`.

Concrete parsimonious parity transport: if a fiber predicate has exactly the image of the
standard SAT accepting assignments under an injective encoding, then its accepting-count parity
is the same as the SAT accepting-count parity. -/
theorem paper_conclusion_periodic_fiber_parity_oplusp_complete {n m : ℕ}
    (satAccepts : Fin n → Bool) (fiberAccepts : Fin m → Bool) (encode : Fin n → Fin m)
    (hencode : Function.Injective encode)
    (hparsimonious :
      (Finset.univ.filter fun y : Fin m => fiberAccepts y) =
        (Finset.univ.filter fun x : Fin n => satAccepts x).image encode) :
    conclusion_periodic_fiber_parity_oplusp_complete_parity_decision fiberAccepts ↔
      conclusion_periodic_fiber_parity_oplusp_complete_parity_decision satAccepts := by
  unfold conclusion_periodic_fiber_parity_oplusp_complete_parity_decision
  rw [hparsimonious, Finset.card_image_of_injective]
  intro x y hxy
  exact hencode hxy

end Omega.Conclusion
