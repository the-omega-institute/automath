import Mathlib.Tactic

namespace Omega.Conclusion

/-- If a visible `mu2` obstruction transfers to an empty observer fiber, then no observer-
equivariant global choice can select one point in every fiber. -/
def conclusion_observer_no_equivariant_choice_under_visible_mu2_statement : Prop :=
  ∀ {Observer : Type*} {Fiber : Observer → Type*}
    (visibleMu2 : Observer → Prop)
    (observerTransport : ∀ i j : Observer, Fiber i → Fiber j),
      (∀ i : Observer, visibleMu2 i → ¬ Nonempty (Fiber i)) →
        (∃ i : Observer, visibleMu2 i) →
          ¬ ∃ choice : ∀ i : Observer, Fiber i,
            ∀ i j : Observer, observerTransport i j (choice i) = choice j

/-- Paper label: `prop:conclusion-observer-no-equivariant-choice-under-visible-mu2`. -/
theorem paper_conclusion_observer_no_equivariant_choice_under_visible_mu2 :
    conclusion_observer_no_equivariant_choice_under_visible_mu2_statement := by
  intro Observer Fiber visibleMu2 observerTransport hempty hvis hchoice
  rcases hvis with ⟨i, hi⟩
  rcases hchoice with ⟨choice, _hequivariant⟩
  exact hempty i hi ⟨choice i⟩

end Omega.Conclusion
