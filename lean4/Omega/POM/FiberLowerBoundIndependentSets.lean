import Mathlib.Data.Fintype.Card

namespace Omega.POM

/-- Paper label: `lem:pom-fiber-lower-bound-independent-sets`. Independent-set witnesses inject
into the fiber by realizing each witness and retaining the proof that it folds to `x`. -/
theorem paper_pom_fiber_lower_bound_independent_sets {Ω X J : Type*} [Fintype Ω]
    [Fintype J] [DecidableEq X] (Fold : Ω → X) (x : X) (realize : J → Ω)
    (hrealize : ∀ S : J, Fold (realize S) = x) (hinj : Function.Injective realize) :
    Fintype.card J ≤ Fintype.card {ω : Ω // Fold ω = x} := by
  let toFiber : J → {ω : Ω // Fold ω = x} := fun S => ⟨realize S, hrealize S⟩
  have htoFiber : Function.Injective toFiber := by
    intro S T hST
    exact hinj (congrArg Subtype.val hST)
  simpa [toFiber] using Fintype.card_le_of_injective toFiber htoFiber

end Omega.POM
