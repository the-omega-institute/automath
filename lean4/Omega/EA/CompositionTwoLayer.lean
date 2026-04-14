import Mathlib.Tactic

namespace Omega.EA.CompositionTwoLayer

/-- The level-0 embedding by function iteration.
    thm:composition-two-layer -/
def iota0 {A : Type _} (g : A → A) (n : ℕ) : A → A :=
  g^[n]

/-- Fresh seed wrapper for the first composition identity.
    thm:composition-two-layer -/
theorem paper_ea_composition_two_layer_seeds
    {A : Type _} (g : A → A) :
    ∀ m n : ℕ, iota0 g (m + n) = iota0 g m ∘ iota0 g n := by
  intro m n
  simpa [iota0] using (Function.iterate_add g m n)

/-- Paper-facing clone wrapper for the composition two-layer seed.
    thm:composition-two-layer -/
theorem paper_ea_composition_two_layer_package
    {A : Type _} (g : A → A) :
    ∀ m n : ℕ, iota0 g (m + n) = iota0 g m ∘ iota0 g n :=
  paper_ea_composition_two_layer_seeds g

end Omega.EA.CompositionTwoLayer
