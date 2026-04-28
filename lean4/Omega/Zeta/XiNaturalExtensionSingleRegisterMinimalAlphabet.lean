import Mathlib.Data.Fintype.EquivFin

namespace Omega.Zeta

open scoped Classical
open Classical

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

/-- Paper label: `prop:xi-natural-extension-single-register-minimal-alphabet`.

For a finite map whose fibers have size at most `M` and whose maximal fiber has size exactly `M`,
choosing an injective alphabet code on every fiber is equivalent to having at least `M` alphabet
symbols. -/
theorem paper_xi_natural_extension_single_register_minimal_alphabet {X A : Type*}
    [Fintype X] [Fintype A] (T : X → X) (M : ℕ)
    (hM : ∀ y : X, Fintype.card {x : X // T x = y} ≤ M)
    (hmax : ∃ y : X, Fintype.card {x : X // T x = y} = M) :
    ((∀ y : X, ∃ ι : {x : X // T x = y} → A, Function.Injective ι) ↔
      M ≤ Fintype.card A) := by
  constructor
  · intro hcodes
    rcases hmax with ⟨y, hy⟩
    rcases hcodes y with ⟨ι, hι⟩
    rw [← hy]
    exact Fintype.card_le_of_injective ι hι
  · intro hA y
    classical
    have hfiber_card : Fintype.card {x : X // T x = y} ≤ Fintype.card A :=
      le_trans (hM y) hA
    rcases Function.Embedding.nonempty_of_card_le
        (α := {x : X // T x = y}) (β := A) hfiber_card with
      ⟨e⟩
    exact ⟨fun x => e x, e.injective⟩

end Omega.Zeta
