import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.OperatorAlgebra

/-- Concrete finite fold data for the fiber-averaging conditional expectation. -/
structure FoldConditionalExpectationData where
  Ω : Type
  X : Type
  instDecEqΩ : DecidableEq Ω
  instFintypeΩ : Fintype Ω
  instDecEqX : DecidableEq X
  instFintypeX : Fintype X
  fold : Ω → X
  fold_surjective : Function.Surjective fold

attribute [instance] FoldConditionalExpectationData.instDecEqΩ
attribute [instance] FoldConditionalExpectationData.instFintypeΩ
attribute [instance] FoldConditionalExpectationData.instDecEqX
attribute [instance] FoldConditionalExpectationData.instFintypeX

namespace FoldConditionalExpectationData

/-- The finite fiber over a fold value. -/
def fiber (D : FoldConditionalExpectationData) (x : D.X) : Finset D.Ω :=
  Finset.univ.filter fun a => D.fold a = x

/-- Fiber cardinality. -/
def fiberCard (D : FoldConditionalExpectationData) (x : D.X) : ℕ :=
  (D.fiber x).card

/-- Fiberwise averaging operator, viewed as an endomorphism of the ambient diagonal algebra. -/
def foldExpectation (D : FoldConditionalExpectationData) (f : D.Ω → ℚ) : D.Ω → ℚ :=
  fun a => Finset.sum (D.fiber (D.fold a)) f / D.fiberCard (D.fold a)

/-- Functions constant on fold fibers. -/
def fiberInvariant (D : FoldConditionalExpectationData) (f : D.Ω → ℚ) : Prop :=
  ∀ a b, D.fold a = D.fold b → f a = f b

/-- Positivity, unitality, and idempotence of the fold-average operator. -/
def positiveUnitalIdempotent (D : FoldConditionalExpectationData) : Prop :=
  (∀ f, (∀ a, 0 ≤ f a) → ∀ a, 0 ≤ D.foldExpectation f a) ∧
    (D.foldExpectation (fun _ => (1 : ℚ)) = fun _ => (1 : ℚ)) ∧
      (∀ f, D.foldExpectation (D.foldExpectation f) = D.foldExpectation f)

/-- The fold-average acts as the identity on the invariant subalgebra. -/
def identityOnInvariantSubalgebra (D : FoldConditionalExpectationData) : Prop :=
  ∀ f, D.fiberInvariant f → D.foldExpectation f = f

/-- Fiberwise averaging is a bimodule map over the invariant subalgebra. -/
def bimoduleLaw (D : FoldConditionalExpectationData) : Prop :=
  ∀ B₁ B₂ A, D.fiberInvariant B₁ → D.fiberInvariant B₂ →
    D.foldExpectation (fun a => B₁ a * A a * B₂ a) =
      fun a => B₁ a * D.foldExpectation A a * B₂ a

lemma mem_fiber_self (D : FoldConditionalExpectationData) (a : D.Ω) :
    a ∈ D.fiber (D.fold a) := by
  simp [fiber]

lemma fiber_nonempty (D : FoldConditionalExpectationData) (x : D.X) : (D.fiber x).Nonempty := by
  rcases D.fold_surjective x with ⟨a, rfl⟩
  exact ⟨a, D.mem_fiber_self a⟩

lemma fiberCard_pos (D : FoldConditionalExpectationData) (x : D.X) : 0 < D.fiberCard x := by
  simpa [fiberCard] using D.fiber_nonempty x |>.card_pos

lemma foldExpectation_fiberInvariant (D : FoldConditionalExpectationData) (f : D.Ω → ℚ) :
    D.fiberInvariant (D.foldExpectation f) := by
  intro a b hab
  simp only [foldExpectation, hab]

lemma sum_eq_card_mul_of_invariant (D : FoldConditionalExpectationData) (f : D.Ω → ℚ)
    (hf : D.fiberInvariant f) (a : D.Ω) :
    Finset.sum (D.fiber (D.fold a)) f = (D.fiberCard (D.fold a) : ℚ) * f a := by
  calc
    Finset.sum (D.fiber (D.fold a)) f = Finset.sum (D.fiber (D.fold a)) (fun _b => f a) := by
      refine Finset.sum_congr rfl ?_
      intro b hb
      exact hf b a (by simpa [fiber] using hb)
    _ = D.fiberCard (D.fold a) * f a := by
      simp [fiberCard]

lemma foldExpectation_eq_self_of_invariant (D : FoldConditionalExpectationData) (f : D.Ω → ℚ)
    (hf : D.fiberInvariant f) : D.foldExpectation f = f := by
  funext a
  have hsum := D.sum_eq_card_mul_of_invariant f hf a
  have hcardq : (D.fiberCard (D.fold a) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (D.fiberCard_pos (D.fold a))
  rw [foldExpectation, hsum]
  field_simp [hcardq]

lemma foldExpectation_pos (D : FoldConditionalExpectationData) (f : D.Ω → ℚ)
    (hf : ∀ a, 0 ≤ f a) (a : D.Ω) : 0 ≤ D.foldExpectation f a := by
  unfold foldExpectation
  refine div_nonneg ?_ ?_
  · exact Finset.sum_nonneg fun b _hb => hf b
  · exact_mod_cast Nat.zero_le (D.fiberCard (D.fold a))

lemma foldExpectation_one (D : FoldConditionalExpectationData) :
    D.foldExpectation (fun _ => (1 : ℚ)) = fun _ => (1 : ℚ) := by
  exact D.foldExpectation_eq_self_of_invariant (fun _ => (1 : ℚ)) (by
    intro a b _hab
    rfl)

lemma foldExpectation_idempotent (D : FoldConditionalExpectationData) (f : D.Ω → ℚ) :
    D.foldExpectation (D.foldExpectation f) = D.foldExpectation f := by
  exact D.foldExpectation_eq_self_of_invariant (D.foldExpectation f) (D.foldExpectation_fiberInvariant f)

lemma foldExpectation_bimodule (D : FoldConditionalExpectationData) (B₁ B₂ A : D.Ω → ℚ)
    (hB₁ : D.fiberInvariant B₁) (hB₂ : D.fiberInvariant B₂) :
    D.foldExpectation (fun a => B₁ a * A a * B₂ a) =
      fun a => B₁ a * D.foldExpectation A a * B₂ a := by
  funext a
  have hcardq : (D.fiberCard (D.fold a) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (D.fiberCard_pos (D.fold a))
  have hsum :
      Finset.sum (D.fiber (D.fold a)) (fun b => B₁ b * A b * B₂ b) =
        B₁ a * Finset.sum (D.fiber (D.fold a)) A * B₂ a := by
    calc
      Finset.sum (D.fiber (D.fold a)) (fun b => B₁ b * A b * B₂ b)
          = Finset.sum (D.fiber (D.fold a)) (fun b => B₁ a * A b * B₂ a) := by
              refine Finset.sum_congr rfl ?_
              intro b hb
              have hfold : D.fold b = D.fold a := by
                simpa [fiber] using hb
              rw [hB₁ b a hfold, hB₂ b a hfold]
      _ = Finset.sum (D.fiber (D.fold a)) (fun b => B₁ a * A b) * B₂ a := by
            rw [Finset.sum_mul]
      _ = (B₁ a * Finset.sum (D.fiber (D.fold a)) A) * B₂ a := by
            rw [Finset.mul_sum]
      _ = B₁ a * Finset.sum (D.fiber (D.fold a)) A * B₂ a := by ring
  rw [foldExpectation, hsum, foldExpectation]
  field_simp [hcardq]

end FoldConditionalExpectationData

open FoldConditionalExpectationData

/-- Paper-facing finite fiber-average conditional expectation package: the fold-average operator is
positive, preserves the unit, is idempotent, restricts to the identity on fiberwise constant
observables, and satisfies the invariant-subalgebra bimodule law.
    prop:fold-conditional-expectation -/
theorem paper_op_algebra_fold_conditional_expectation (D : FoldConditionalExpectationData) :
    D.positiveUnitalIdempotent ∧ D.identityOnInvariantSubalgebra ∧ D.bimoduleLaw := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, D.foldExpectation_one, ?_⟩
    · intro f hf a
      exact D.foldExpectation_pos f hf a
    · intro f
      exact D.foldExpectation_idempotent f
  · intro f hf
    exact D.foldExpectation_eq_self_of_invariant f hf
  · intro B₁ B₂ A hB₁ hB₂
    exact D.foldExpectation_bimodule B₁ B₂ A hB₁ hB₂

/-- prop:fold-conditional-expectation -/
theorem paper_fold_conditional_expectation (D : FoldConditionalExpectationData) :
    D.positiveUnitalIdempotent ∧ D.identityOnInvariantSubalgebra ∧ D.bimoduleLaw := by
  exact paper_op_algebra_fold_conditional_expectation D

end Omega.OperatorAlgebra
