import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped Classical

/-- The finite truncation receiver for the mixed hidden state: `β` binary hidden generators
together with one cyclic truncation coordinate of order `N`. -/
abbrev conclusion_mixed_hiddenstate_finite_truncation_hom_count_receiver
    (beta N : ℕ) : Type :=
  (Fin beta → ZMod 2) × ZMod N

/-- The `n`-torsion subtype in an additive target group. -/
def conclusion_mixed_hiddenstate_finite_truncation_hom_count_torsion
    (G : Type*) [AddMonoid G] (n : ℕ) : Type _ :=
  {g : G // n • g = 0}

noncomputable instance conclusion_mixed_hiddenstate_finite_truncation_hom_count_torsion_fintype
    (G : Type*) [AddMonoid G] [Fintype G] (n : ℕ) :
    Fintype (conclusion_mixed_hiddenstate_finite_truncation_hom_count_torsion G n) := by
  exact Fintype.ofInjective (fun g => g.1) (fun _ _ h => Subtype.ext h)

/-- Concrete hom data out of the finite truncation receiver: the images of the `β` binary
generators, each satisfying the `2`-torsion relation, and the image of the cyclic generator,
satisfying the `N`-torsion relation. -/
structure conclusion_mixed_hiddenstate_finite_truncation_hom_count_hom_data
    (beta N : ℕ) (G : Type*) [AddMonoid G] where
  hidden :
    Fin beta → conclusion_mixed_hiddenstate_finite_truncation_hom_count_torsion G 2
  cyclic : conclusion_mixed_hiddenstate_finite_truncation_hom_count_torsion G N

/-- The product-universal-property splitting of finite-truncation hom data. -/
def conclusion_mixed_hiddenstate_finite_truncation_hom_count_hom_split
    (beta N : ℕ) (G : Type*) [AddMonoid G] :
    conclusion_mixed_hiddenstate_finite_truncation_hom_count_hom_data beta N G ≃
      (Fin beta → conclusion_mixed_hiddenstate_finite_truncation_hom_count_torsion G 2) ×
        conclusion_mixed_hiddenstate_finite_truncation_hom_count_torsion G N where
  toFun h := (h.hidden, h.cyclic)
  invFun p := ⟨p.1, p.2⟩
  left_inv h := by
    cases h
    rfl
  right_inv p := by
    cases p
    rfl

noncomputable instance conclusion_mixed_hiddenstate_finite_truncation_hom_count_hom_data_fintype
    (beta N : ℕ) (G : Type*) [AddMonoid G] [Fintype G] :
    Fintype (conclusion_mixed_hiddenstate_finite_truncation_hom_count_hom_data beta N G) :=
  Fintype.ofEquiv
    ((Fin beta → conclusion_mixed_hiddenstate_finite_truncation_hom_count_torsion G 2) ×
      conclusion_mixed_hiddenstate_finite_truncation_hom_count_torsion G N)
    (conclusion_mixed_hiddenstate_finite_truncation_hom_count_hom_split beta N G).symm

/-- Paper-facing statement for the finite truncation hom-count formula. -/
def conclusion_mixed_hiddenstate_finite_truncation_hom_count_statement
    (beta N : ℕ) : Prop :=
  ∀ G : Type*, ∀ [AddCommMonoid G], ∀ [Fintype G],
    Nonempty
      (conclusion_mixed_hiddenstate_finite_truncation_hom_count_hom_data beta N G ≃
        (Fin beta → conclusion_mixed_hiddenstate_finite_truncation_hom_count_torsion G 2) ×
          conclusion_mixed_hiddenstate_finite_truncation_hom_count_torsion G N) ∧
      Fintype.card
          (conclusion_mixed_hiddenstate_finite_truncation_hom_count_hom_data beta N G) =
        Fintype.card
            (conclusion_mixed_hiddenstate_finite_truncation_hom_count_torsion G 2) ^ beta *
          Fintype.card
            (conclusion_mixed_hiddenstate_finite_truncation_hom_count_torsion G N)

/-- Paper label: `thm:conclusion-mixed-hiddenstate-finite-truncation-hom-count`. -/
theorem paper_conclusion_mixed_hiddenstate_finite_truncation_hom_count (beta N : ℕ) :
    conclusion_mixed_hiddenstate_finite_truncation_hom_count_statement beta N := by
  intro G _ _
  refine ⟨⟨conclusion_mixed_hiddenstate_finite_truncation_hom_count_hom_split beta N G⟩, ?_⟩
  rw [Fintype.card_congr
    (conclusion_mixed_hiddenstate_finite_truncation_hom_count_hom_split beta N G)]
  simp [Fintype.card_prod]

end Omega.Conclusion
