import Mathlib

namespace Omega.Conclusion

open scoped Classical

noncomputable section

theorem paper_conclusion_screen_padic_hidden_entropy_law {p : ℕ} [Fact p.Prime] {V W : Type*}
    [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V] [Fintype V]
    [AddCommGroup W] [Module (ZMod p) W] (f : V →ₗ[ZMod p] W) :
    ∃ r : ℕ, ∀ y : LinearMap.range f, Fintype.card {x : V // f x = y.1} = p ^ r := by
  classical
  let r : ℕ := Module.finrank (ZMod p) (LinearMap.ker f)
  refine ⟨r, ?_⟩
  intro y
  rcases y with ⟨y, ⟨x₀, rfl⟩⟩
  let e : {x : V // f x = f x₀} ≃ LinearMap.ker f :=
    { toFun := fun x =>
        ⟨x.1 - x₀, by
          show f (x.1 - x₀) = 0
          rw [map_sub, x.2, sub_self]⟩
      invFun := fun z =>
        ⟨x₀ + z.1, by
          have hz : f z.1 = 0 := by
            exact z.2
          rw [map_add, hz, add_zero]⟩
      left_inv := by
        intro x
        apply Subtype.ext
        change x₀ + (x.1 - x₀) = x.1
        abel
      right_inv := by
        intro z
        apply Subtype.ext
        change x₀ + z.1 - x₀ = z.1
        abel }
  calc
    Fintype.card {x : V // f x = f x₀} = Fintype.card (LinearMap.ker f) := Fintype.card_congr e
    _ = p ^ r := by
      simpa [r, ZMod.card p] using
        (Module.card_eq_pow_finrank (K := ZMod p) (V := LinearMap.ker f))

end

end Omega.Conclusion
