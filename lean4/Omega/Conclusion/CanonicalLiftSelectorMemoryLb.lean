import Mathlib.Tactic

namespace Omega.Conclusion.CanonicalLiftSelectorMemoryLb

/-- Injective-on-finset image has same cardinality as the source.
    cor:conclusion-canonical-lift-selector-memory-lb -/
theorem card_image_of_injOn {α S : Type*} [DecidableEq S]
    (T : Finset α) (f : α → S)
    (hinj : ∀ x ∈ T, ∀ y ∈ T, f x = f y → x = y) :
    (T.image f).card = T.card :=
  Finset.card_image_of_injOn hinj

/-- Injection from a finset to a fintype implies cardinality bound.
    cor:conclusion-canonical-lift-selector-memory-lb -/
theorem paper_conclusion_canonical_lift_selector_memory_lb
    {α S : Type*} [DecidableEq α] [DecidableEq S] [Fintype S]
    (T : Finset α) (f : α → S)
    (hinj : ∀ x ∈ T, ∀ y ∈ T, f x = f y → x = y) :
    T.card ≤ Fintype.card S := by
  calc T.card = (T.image f).card := (card_image_of_injOn T f hinj).symm
    _ ≤ Fintype.card S := Finset.card_le_univ _

end Omega.Conclusion.CanonicalLiftSelectorMemoryLb
