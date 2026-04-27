import Mathlib.Data.Set.Basic

namespace Omega.RecursiveAddressing

/-- Paper label: `prop:observer-indexed-global-layer-logic-only`. -/
theorem paper_observer_indexed_global_layer_logic_only
    {State Formula : Type*} (Forces : State → Formula → Prop)
    (Derives : Set Formula → Formula → Prop) {Γ : Set Formula} {φ : Formula}
    (sound : Derives Γ φ → ∀ p, (∀ γ, γ ∈ Γ → Forces p γ) → Forces p φ)
    (hder : Derives Γ φ) :
    ∀ p, (∀ γ, γ ∈ Γ → Forces p γ) → Forces p φ := by
  exact sound hder

end Omega.RecursiveAddressing
