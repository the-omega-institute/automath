import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-observer-hidden-register-sharp-capacity`.
An encoding into `A_vis × R` that preserves the visible quotient must inject each fixed visible
fiber into `R`. If `A` already splits as `A_vis × H`, this forces `|H| ≤ |R|`, and the split map
itself realizes the sharp embedding into `A_vis × H`. -/
theorem paper_conclusion_observer_hidden_register_sharp_capacity
    {A Avis H R : Type*} [Fintype A] [Fintype Avis] [Fintype H] [Fintype R] [Nonempty Avis]
    (π : A → Avis)
    (conclusion_observer_hidden_register_sharp_capacity_split : A ≃ Avis × H)
    (hπ : ∀ a, (conclusion_observer_hidden_register_sharp_capacity_split a).1 = π a)
    (ι : A → Avis × R) (hι : Function.Injective ι) (hιπ : ∀ a, (ι a).1 = π a) :
    Fintype.card H ≤ Fintype.card R ∧
      ∃ j : A → Avis × H, Function.Injective j ∧ ∀ a, (j a).1 = π a := by
  obtain ⟨x0⟩ := ‹Nonempty Avis›
  let fiberRegister : H → R := fun h =>
    (ι (conclusion_observer_hidden_register_sharp_capacity_split.symm (x0, h))).2
  have hFiberRegister : Function.Injective fiberRegister := by
    intro h₁ h₂ hh
    have hEncodeEq :
        ι (conclusion_observer_hidden_register_sharp_capacity_split.symm (x0, h₁)) =
          ι (conclusion_observer_hidden_register_sharp_capacity_split.symm (x0, h₂)) := by
      apply Prod.ext
      · calc
          (ι (conclusion_observer_hidden_register_sharp_capacity_split.symm (x0, h₁))).1
              = π (conclusion_observer_hidden_register_sharp_capacity_split.symm (x0, h₁)) := by
                rw [hιπ]
          _ = x0 := by rw [← hπ]; simp
          _ = π (conclusion_observer_hidden_register_sharp_capacity_split.symm (x0, h₂)) := by
                rw [← hπ]; simp
          _ = (ι (conclusion_observer_hidden_register_sharp_capacity_split.symm (x0, h₂))).1 := by
                rw [hιπ]
      · simpa [fiberRegister] using hh
    have hPreimageEq :
        conclusion_observer_hidden_register_sharp_capacity_split.symm (x0, h₁) =
          conclusion_observer_hidden_register_sharp_capacity_split.symm (x0, h₂) :=
      hι hEncodeEq
    have hPairEq : (x0, h₁) = (x0, h₂) := by
      simpa using congrArg conclusion_observer_hidden_register_sharp_capacity_split hPreimageEq
    simpa using congrArg Prod.snd hPairEq
  have hLower : Fintype.card H ≤ Fintype.card R :=
    Fintype.card_le_of_injective fiberRegister hFiberRegister
  refine ⟨hLower, ?_⟩
  exact
    ⟨conclusion_observer_hidden_register_sharp_capacity_split,
      conclusion_observer_hidden_register_sharp_capacity_split.injective, hπ⟩

end Omega.Conclusion
