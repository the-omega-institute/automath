import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

namespace Omega.Zeta

/-- The fiber of a stage map `π : X → Y` over `y`. -/
def LayerFiber {X Y : Type*} (π : X → Y) (y : Y) := { x : X // π x = y }

/-- A labeling is locally invertible when it is injective on every fiber. -/
def FiberwiseInjective {X Y Λ : Type*} (π : X → Y) (q : X → Λ) : Prop :=
  ∀ y, Function.Injective fun x : LayerFiber π y => q x.1

/-- A finite-fiber layer admits a locally invertible alphabet of size `|Λ|` exactly when
the maximal fiber size is at most `|Λ|`.
This packages the lower bound from the maximal fiber and the upper bound from fiberwise
embeddings into the chosen alphabet.
    thm:xi-layered-primeslice-local-alphabet-fibermax -/
theorem paper_xi_layered_primeslice_local_alphabet_fibermax
    {X Y Λ : Type*} [Fintype X] [Fintype Λ]
    (π : X → Y) (B : ℕ)
    (hmax : ∀ y, Nat.card (LayerFiber π y) ≤ B)
    (hwit : ∃ y, Nat.card (LayerFiber π y) = B) :
    (∃ q : X → Λ, FiberwiseInjective π q) ↔ B ≤ Fintype.card Λ := by
  constructor
  · rintro ⟨q, hq⟩
    rcases hwit with ⟨y, hy⟩
    let e : LayerFiber π y ↪ Λ := ⟨fun x => q x.1, hq y⟩
    rw [← hy]
    simpa [Nat.card_eq_fintype_card] using Finite.card_le_of_embedding e
  · intro hΛ
    classical
    let e : ∀ y, LayerFiber π y ↪ Λ := fun y =>
      let _ : Finite (LayerFiber π y) := Finite.of_injective (fun x : LayerFiber π y => x.1)
        Subtype.val_injective
      let _ : Fintype (LayerFiber π y) := Fintype.ofFinite (LayerFiber π y)
      Classical.choice <| Function.Embedding.nonempty_of_card_le <|
        by simpa [Nat.card_eq_fintype_card] using Nat.le_trans (hmax y) hΛ
    refine ⟨fun x => e (π x) ⟨x, rfl⟩, ?_⟩
    intro y x₁ x₂ hq
    cases x₁ with
    | mk x₁ hx₁ =>
      cases x₂ with
      | mk x₂ hx₂ =>
        have hx₁' : e (π x₁) ⟨x₁, rfl⟩ = e y ⟨x₁, hx₁⟩ := by
          cases hx₁
          rfl
        have hx₂' : e (π x₂) ⟨x₂, rfl⟩ = e y ⟨x₂, hx₂⟩ := by
          cases hx₂
          rfl
        have hq' : e y ⟨x₁, hx₁⟩ = e y ⟨x₂, hx₂⟩ := by
          calc
            e y ⟨x₁, hx₁⟩ = e (π x₁) ⟨x₁, rfl⟩ := hx₁'.symm
            _ = e (π x₂) ⟨x₂, rfl⟩ := hq
            _ = e y ⟨x₂, hx₂⟩ := hx₂'
        apply Subtype.ext
        exact congrArg Subtype.val ((e y).injective hq')

end Omega.Zeta
