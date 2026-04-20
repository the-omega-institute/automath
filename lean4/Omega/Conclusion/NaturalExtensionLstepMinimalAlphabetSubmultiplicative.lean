import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic
import Omega.Zeta.LayeredPrimesliceLocalAlphabetFibermax

namespace Omega.Conclusion

/-- `thm:conclusion-natural-extension-lstep-minimal-alphabet-submultiplicative` -/
theorem paper_conclusion_natural_extension_lstep_minimal_alphabet_submultiplicative
    {X A : Type*} [Fintype X] [Fintype A]
    (T : X → X) (l r Dl Dr : ℕ)
    (hlmax : ∀ y, Nat.card (Omega.Zeta.LayerFiber (T^[l]) y) ≤ Dl)
    (hlwit : ∃ y, Nat.card (Omega.Zeta.LayerFiber (T^[l]) y) = Dl)
    (hrmax : ∀ y, Nat.card (Omega.Zeta.LayerFiber (T^[r]) y) ≤ Dr)
    (hrwit : ∃ y, Nat.card (Omega.Zeta.LayerFiber (T^[r]) y) = Dr) :
    ((∃ q : X → A, Omega.Zeta.FiberwiseInjective (T^[l]) q) ↔ Dl ≤ Fintype.card A) ∧
      (∀ y, Nat.card (Omega.Zeta.LayerFiber (T^[l + r]) y) ≤ Dl * Dr) := by
  have _ := hrwit
  constructor
  · simpa using
      (Omega.Zeta.paper_xi_layered_primeslice_local_alphabet_fibermax
        (Λ := A) (π := T^[l]) (B := Dl) hlmax hlwit)
  · intro y
    classical
    let _ : Finite (Omega.Zeta.LayerFiber (T^[l]) y) :=
      Finite.of_injective (fun x : Omega.Zeta.LayerFiber (T^[l]) y => x.1) Subtype.val_injective
    let _ : Fintype (Omega.Zeta.LayerFiber (T^[l]) y) :=
      Fintype.ofFinite (Omega.Zeta.LayerFiber (T^[l]) y)
    let _ : ∀ z : Omega.Zeta.LayerFiber (T^[l]) y, Finite (Omega.Zeta.LayerFiber (T^[r]) z.1) :=
      fun z =>
        Finite.of_injective (fun x : Omega.Zeta.LayerFiber (T^[r]) z.1 => x.1)
          Subtype.val_injective
    let e : Omega.Zeta.LayerFiber (T^[l + r]) y ≃
        Sigma (fun z : Omega.Zeta.LayerFiber (T^[l]) y => Omega.Zeta.LayerFiber (T^[r]) z.1) :=
      { toFun := fun x =>
          ⟨⟨(T^[r]) x.1, by simpa [Function.iterate_add_apply] using x.2⟩, ⟨x.1, rfl⟩⟩
        invFun := fun s =>
          match s with
          | ⟨⟨z, hz⟩, ⟨x, hx⟩⟩ => ⟨x, by simpa [Function.iterate_add_apply, hx] using hz⟩
        left_inv := by
          intro x
          cases x
          rfl
        right_inv := by
          intro s
          cases s with
          | mk z x =>
              cases z with
              | mk z hz =>
                  cases x with
                  | mk x hx =>
                      dsimp
                      have hz' :
                          (⟨T^[r] x, by simpa [Function.iterate_add_apply, hx] using hz⟩ :
                            Omega.Zeta.LayerFiber (T^[l]) y) = ⟨z, hz⟩ := by
                        apply Subtype.ext
                        exact hx
                      cases hz'
                      rfl }
    calc
      Nat.card (Omega.Zeta.LayerFiber (T^[l + r]) y)
          = Nat.card
              (Sigma
                (fun z : Omega.Zeta.LayerFiber (T^[l]) y =>
                  Omega.Zeta.LayerFiber (T^[r]) z.1)) := Nat.card_congr e
      _ = ∑ z : Omega.Zeta.LayerFiber (T^[l]) y, Nat.card (Omega.Zeta.LayerFiber (T^[r]) z.1) := by
            simpa using
              (Nat.card_sigma (α := Omega.Zeta.LayerFiber (T^[l]) y)
                (β := fun z : Omega.Zeta.LayerFiber (T^[l]) y =>
                  Omega.Zeta.LayerFiber (T^[r]) z.1))
      _ ≤ ∑ z : Omega.Zeta.LayerFiber (T^[l]) y, Dr := by
            exact Finset.sum_le_sum (fun z _ => hrmax z.1)
      _ = Fintype.card (Omega.Zeta.LayerFiber (T^[l]) y) * Dr := by
            simp
      _ ≤ Dl * Dr := by
            exact Nat.mul_le_mul_right Dr (by
              simpa [Nat.card_eq_fintype_card] using hlmax y)

end Omega.Conclusion
