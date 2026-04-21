import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Choosing a section of `F` is equivalent to choosing, for each `x`, one element of the fiber
`F⁻¹({x})`. -/
def microcanonicalSectionEquiv {A X : Type*} [Fintype A] [Fintype X] [DecidableEq A]
    [DecidableEq X] (F : A → X) :
    {s : X → A // F ∘ s = id} ≃ ((x : X) → {a : A // F a = x}) where
  toFun s x := ⟨s.1 x, by
    simpa [Function.comp] using congrFun s.2 x⟩
  invFun t :=
    ⟨fun x => (t x).1, funext fun x => (t x).2⟩
  left_inv s := by
    rcases s with ⟨s, hs⟩
    rfl
  right_inv t := by
    funext x
    apply Subtype.ext
    rfl

/-- Paper label: `thm:pom-microcanonical-section-count`.
The number of sections of a finite map is the product of the fiber cardinalities. -/
theorem paper_pom_microcanonical_section_count {A X : Type*} [Fintype A] [Fintype X]
    [DecidableEq A] [DecidableEq X] (F : A → X) :
    Fintype.card {s : X → A // F ∘ s = id} = ∏ x : X, Fintype.card {a : A // F a = x} := by
  rw [Fintype.card_congr (microcanonicalSectionEquiv F), Fintype.card_pi]

end Omega.POM
