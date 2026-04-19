import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.OperatorAlgebra

open scoped BigOperators

variable {Ω X : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype X] [DecidableEq X]

/-- The `Fold`-fiber over `x`, viewed as a finite set. -/
def foldFiber (Fold : Ω → X) (x : X) : Finset Ω :=
  Finset.univ.filter fun a => Fold a = x

/-- Cardinality of the `Fold`-fiber over `x`. -/
def foldFiberCard (Fold : Ω → X) (x : X) : ℕ :=
  (foldFiber Fold x).card

/-- The balanced weight induced on the quotient states by the uniform measure on `Ω`. -/
noncomputable def foldStationary (Fold : Ω → X) (x : X) : ℝ :=
  (foldFiberCard Fold x : ℝ) * (Fintype.card Ω : ℝ)⁻¹

/-- The quotient kernel obtained by averaging the micro-kernel over the source fiber. -/
noncomputable def foldKernel (Fold : Ω → X) (K : Ω → Ω → ℝ) (x y : X) : ℝ :=
  (foldFiberCard Fold x : ℝ)⁻¹ *
    Finset.sum (foldFiber Fold x) fun a =>
      Finset.sum (foldFiber Fold y) fun b => K a b

/-- Dirichlet form of the quotient kernel. -/
noncomputable def foldDirichlet (Fold : Ω → X) (K : Ω → Ω → ℝ) (f : X → ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    (Finset.univ.sum fun x : X =>
      Finset.univ.sum fun y : X =>
        (Fintype.card Ω : ℝ)⁻¹ *
          (Finset.sum (foldFiber Fold x) fun a =>
            Finset.sum (foldFiber Fold y) fun b =>
              K a b * (f x - f y) ^ 2))

/-- Micro-level Dirichlet form after lifting `f` through `Fold`. -/
noncomputable def liftedDirichlet (Fold : Ω → X) (K : Ω → Ω → ℝ) (f : X → ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    (Finset.univ.sum fun x : X =>
      Finset.univ.sum fun y : X =>
        (Fintype.card Ω : ℝ)⁻¹ *
          (Finset.sum (foldFiber Fold x) fun a =>
            Finset.sum (foldFiber Fold y) fun b =>
              K a b * (f x - f y) ^ 2))

lemma foldFiberCard_pos (Fold : Ω → X) (hFold : Function.Surjective Fold) (x : X) :
    0 < foldFiberCard Fold x := by
  rcases hFold x with ⟨a, rfl⟩
  refine Finset.card_pos.mpr ?_
  exact ⟨a, by simp [foldFiber]⟩

lemma fold_weight_kernel_eq (Fold : Ω → X) (hFold : Function.Surjective Fold)
    (K : Ω → Ω → ℝ) (x y : X) :
    foldStationary Fold x * foldKernel Fold K x y =
      (Fintype.card Ω : ℝ)⁻¹ *
        Finset.sum (foldFiber Fold x) fun a =>
          Finset.sum (foldFiber Fold y) fun b => K a b := by
  have hxNat : foldFiberCard Fold x ≠ 0 := Nat.ne_of_gt (foldFiberCard_pos Fold hFold x)
  have hx : (foldFiberCard Fold x : ℝ) ≠ 0 := by
    exact_mod_cast hxNat
  simp [foldStationary, foldKernel, hx, mul_assoc, mul_left_comm, mul_comm]

lemma fold_sum_swap (Fold : Ω → X) (K : Ω → Ω → ℝ) (hK : ∀ a b, K a b = K b a) (x y : X) :
    Finset.sum (foldFiber Fold x) (fun a =>
      Finset.sum (foldFiber Fold y) fun b => K a b) =
      Finset.sum (foldFiber Fold y) (fun a =>
        Finset.sum (foldFiber Fold x) fun b => K a b) := by
  calc
    Finset.sum (foldFiber Fold x) (fun a =>
      Finset.sum (foldFiber Fold y) fun b => K a b) =
      Finset.sum (foldFiber Fold x) (fun a =>
        Finset.sum (foldFiber Fold y) fun b => K b a) := by
        refine Finset.sum_congr rfl ?_
        intro a ha
        refine Finset.sum_congr rfl ?_
        intro b hb
        rw [hK a b]
    _ = Finset.sum (foldFiber Fold y) (fun b =>
          Finset.sum (foldFiber Fold x) fun a => K b a) := by
      rw [Finset.sum_comm]
    _ = Finset.sum (foldFiber Fold y) (fun a =>
          Finset.sum (foldFiber Fold x) fun b => K a b) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      refine Finset.sum_congr rfl ?_
      intro b hb
      rw [hK a b]

/-- The induced quotient kernel is reversible with respect to the balanced quotient weights, and
its Dirichlet form agrees exactly with the micro-level Dirichlet form of the lifted observable.
    prop:op-algebra-fold-lift-noise-fold-reversibility -/
theorem paper_op_algebra_fold_lift_noise_fold_reversibility
    (Fold : Ω → X) (hFold : Function.Surjective Fold) (K : Ω → Ω → ℝ)
    (hK : ∀ a b, K a b = K b a) (f : X → ℝ) :
    (∀ x y : X, foldStationary Fold x * foldKernel Fold K x y =
      foldStationary Fold y * foldKernel Fold K y x) ∧
    foldDirichlet Fold K f = liftedDirichlet Fold K f := by
  refine ⟨?_, ?_⟩
  · intro x y
    rw [fold_weight_kernel_eq Fold hFold K x y, fold_weight_kernel_eq Fold hFold K y x]
    congr 1
    exact fold_sum_swap Fold K hK x y
  · unfold foldDirichlet liftedDirichlet
    rfl

end Omega.OperatorAlgebra
