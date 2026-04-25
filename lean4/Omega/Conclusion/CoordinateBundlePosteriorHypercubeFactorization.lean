import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-coordinate-bundle-posterior-hypercube-factorization`.
The hypotheses package a fiber as an affine `ZMod 2` coordinate cube, giving an explicit
equivalence between the subtype fiber and the bit-vector space. -/
theorem paper_conclusion_coordinate_bundle_posterior_hypercube_factorization {V W : Type*}
    [AddCommGroup V] (T : V → W) (L_J : ℕ) («section» : W → V)
    (coord : (Fin L_J → ZMod 2) → V)
    (hfiber : ∀ y x, T x = y ↔ ∃ ε, x = «section» y + coord ε)
    (huniq : ∀ y ε η, «section» y + coord ε = «section» y + coord η → ε = η) :
    ∀ y, Nonempty ({x : V // T x = y} ≃ (Fin L_J → ZMod 2)) := by
  intro y
  refine ⟨
    { toFun := fun x => Classical.choose ((hfiber y x.1).mp x.2)
      invFun := fun ε =>
        ⟨«section» y + coord ε, (hfiber y («section» y + coord ε)).mpr ⟨ε, rfl⟩⟩
      left_inv := ?_
      right_inv := ?_ }⟩
  · intro x
    apply Subtype.ext
    exact (Classical.choose_spec ((hfiber y x.1).mp x.2)).symm
  · intro ε
    have hy : T («section» y + coord ε) = y :=
      (hfiber y («section» y + coord ε)).mpr ⟨ε, rfl⟩
    exact huniq y (Classical.choose ((hfiber y («section» y + coord ε)).mp hy)) ε
      (Classical.choose_spec ((hfiber y («section» y + coord ε)).mp hy)).symm

end Omega.Conclusion
