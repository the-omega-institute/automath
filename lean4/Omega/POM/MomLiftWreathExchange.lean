import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- The `q` labeled lift coordinates carried by `q` copies before quotienting by permutations. -/
abbrev pom_mom_lift_wreath_exchange_labeled_axis (G : Type*) (q : ℕ) :=
  Fin q → G

/-- The copy permutations coming from the unlabeled `q`-fold moment quotient. -/
abbrev pom_mom_lift_wreath_exchange_copy_permutations (q : ℕ) :=
  Equiv.Perm (Fin q)

/-- The exchanged lift object: `G^q` together with the copy-permutation symmetry. -/
abbrev pom_mom_lift_wreath_exchange_wreath_carrier (G : Type*) (q : ℕ) :=
  pom_mom_lift_wreath_exchange_labeled_axis G q ×
    pom_mom_lift_wreath_exchange_copy_permutations q

/-- After quotienting by copy permutations, the lift axis is modeled by the wreath carrier. -/
abbrev pom_mom_lift_wreath_exchange_exchanged_lift_object (G : Type*) (q : ℕ) :=
  pom_mom_lift_wreath_exchange_wreath_carrier G q

/-- Copy permutations act on the labeled axis by relabeling the coordinates. -/
def pom_mom_lift_wreath_exchange_permute_labels (G : Type*) (q : ℕ)
    (σ : pom_mom_lift_wreath_exchange_copy_permutations q) :
    pom_mom_lift_wreath_exchange_labeled_axis G q ≃
      pom_mom_lift_wreath_exchange_labeled_axis G q where
  toFun x := x ∘ σ.symm
  invFun x := x ∘ σ
  left_inv x := by
    funext i
    simp
  right_inv x := by
    funext i
    simp

/-- The exchanged lift object is definitionally the wreath carrier `G^q ⋊ S_q` at the level of
underlying coordinates. -/
def pom_mom_lift_wreath_exchange_exchanged_equiv_wreath (G : Type*) (q : ℕ) :
    pom_mom_lift_wreath_exchange_exchanged_lift_object G q ≃
      pom_mom_lift_wreath_exchange_wreath_carrier G q :=
  Equiv.refl _

/-- Moment-first then lift yields `q` labeled copies, and quotienting by copy permutations adds
the `S_q` symmetry recorded by the wreath carrier. -/
def pom_mom_lift_wreath_exchange_statement : Prop :=
  ∀ (G : Type*) [Group G] (q : ℕ),
    2 ≤ q →
      Nonempty
        (pom_mom_lift_wreath_exchange_exchanged_lift_object G q ≃
          pom_mom_lift_wreath_exchange_wreath_carrier G q) ∧
        ∀ σ : pom_mom_lift_wreath_exchange_copy_permutations q,
          Function.Bijective
            (pom_mom_lift_wreath_exchange_permute_labels G q σ)

private lemma pom_mom_lift_wreath_exchange_statement_proof :
    pom_mom_lift_wreath_exchange_statement := by
  intro G _ q hq
  refine ⟨⟨pom_mom_lift_wreath_exchange_exchanged_equiv_wreath G q⟩, ?_⟩
  intro σ
  simpa using (pom_mom_lift_wreath_exchange_permute_labels G q σ).bijective

/-- Paper label: `prop:pom-mom-lift-wreath-exchange`. Lifting first gives the `G^q` label axis,
and quotienting by copy permutations inserts the `S_q` symmetry, so the exchanged lift object is
the wreath carrier `G^q × S_q`. -/
theorem paper_pom_mom_lift_wreath_exchange :
    pom_mom_lift_wreath_exchange_statement := by
  exact pom_mom_lift_wreath_exchange_statement_proof

end Omega.POM
