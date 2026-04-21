import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldLiftGlobalSignFactorization

namespace Omega.OperatorAlgebra

open scoped BigOperators

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

noncomputable def hiddenAutomorphismSign {m : ℕ} (d : Fin m → ℕ)
    (ψ : HiddenFiberAutomorphisms d) : ℤˣ :=
  ∏ x, Equiv.Perm.sign (ψ x)

noncomputable def flipHidden {m : ℕ} (d : Fin m → ℕ) (x0 : Fin m)
    (σ : Equiv.Perm (Fin (d x0))) : HiddenFiberAutomorphisms d → HiddenFiberAutomorphisms d :=
  fun ψ => Function.update ψ x0 (σ * ψ x0)

noncomputable def flipLift {m : ℕ} (d : Fin m → ℕ) (x0 : Fin m)
    (σ : Equiv.Perm (Fin (d x0))) : FoldFiberNormalizer d → FoldFiberNormalizer d :=
  fun τ => (τ.1, flipHidden d x0 σ τ.2)

@[simp] theorem visibleProjection_flipLift {m : ℕ} (d : Fin m → ℕ) (x0 : Fin m)
    (σ : Equiv.Perm (Fin (d x0))) (τ : FoldFiberNormalizer d) :
    visibleProjection d (flipLift d x0 σ τ) = visibleProjection d τ :=
  rfl

@[simp] theorem hiddenFiberProductSign_mk {m : ℕ} (d : Fin m → ℕ)
    (f : CompatibleVisiblePerm d) (ψ : HiddenFiberAutomorphisms d) :
    hiddenFiberProductSign d (f, ψ) = hiddenAutomorphismSign d ψ :=
  rfl

theorem hiddenAutomorphismSign_flipHidden {m : ℕ} (d : Fin m → ℕ) (x0 : Fin m)
    (σ : Equiv.Perm (Fin (d x0))) (ψ : HiddenFiberAutomorphisms d) :
    hiddenAutomorphismSign d (flipHidden d x0 σ ψ) =
      Equiv.Perm.sign σ * hiddenAutomorphismSign d ψ := by
  classical
  unfold hiddenAutomorphismSign flipHidden
  have hupdate :
      (fun x : Fin m => Equiv.Perm.sign (Function.update ψ x0 (σ * ψ x0) x)) =
        Function.update (fun y : Fin m => Equiv.Perm.sign (ψ y)) x0
          (Equiv.Perm.sign (σ * ψ x0)) := by
    funext x
    by_cases hx : x = x0
    · subst hx
      simp
    · simp [Function.update, hx]
  rw [hupdate, Finset.prod_update_of_mem (s := Finset.univ) (i := x0) (by simp), Equiv.Perm.sign_mul]
  calc
    Equiv.Perm.sign σ * Equiv.Perm.sign (ψ x0) *
        ∏ x ∈ Finset.univ \ {x0}, Equiv.Perm.sign (ψ x)
        = Equiv.Perm.sign σ *
            (Equiv.Perm.sign (ψ x0) * ∏ x ∈ Finset.univ.erase x0, Equiv.Perm.sign (ψ x)) := by
              simp [mul_assoc]
    _ = Equiv.Perm.sign σ * ∏ x, Equiv.Perm.sign (ψ x) := by
          rw [Finset.mul_prod_erase (s := Finset.univ) (f := fun x : Fin m => Equiv.Perm.sign (ψ x))
            (a := x0) (by simp)]

theorem foldFiberNormalizerSign_flipLift {m : ℕ} (d : Fin m → ℕ) (x0 : Fin m)
    (σ : Equiv.Perm (Fin (d x0))) (τ : FoldFiberNormalizer d) :
    foldFiberNormalizerSign d (flipLift d x0 σ τ) =
      Equiv.Perm.sign σ * foldFiberNormalizerSign d τ := by
  cases τ with
  | mk f ψ =>
      simp [flipLift, foldFiberNormalizerSign, hiddenFactor, visibleProjection, visibleSection,
        visibleOddBlockSign, hiddenAutomorphismSign_flipHidden, mul_assoc, mul_left_comm, mul_comm]

theorem flipLift_involutive {m : ℕ} (d : Fin m → ℕ) (x0 : Fin m)
    (σ : Equiv.Perm (Fin (d x0))) (hσsq : σ * σ = 1) :
    Function.Involutive (flipLift d x0 σ) := by
  intro τ
  cases τ with
  | mk f ψ =>
      apply Prod.ext
      · rfl
      · funext y
        by_cases hy : y = x0
        · subst hy
          simp [flipLift, flipHidden]
          rw [← mul_assoc, hσsq, one_mul]
        · simp [flipLift, flipHidden, hy]

/-- If one hidden fiber has size at least `2`, then composing every lift with a fixed hidden
transposition gives a sign-reversing involution on the fiber over any visible permutation.
    cor:op-algebra-fold-alternating-lift-counting -/
theorem paper_op_algebra_fold_alternating_lift_counting {m : Nat}
    (d : Fin m -> Nat) (f : CompatibleVisiblePerm d) (hlarge : ∃ x, 2 <= d x) :
    Fintype.card {tau : FoldFiberNormalizer d //
        visibleProjection d tau = f ∧ foldFiberNormalizerSign d tau = 1} =
      Fintype.card {tau : FoldFiberNormalizer d //
        visibleProjection d tau = f ∧ foldFiberNormalizerSign d tau = -1} := by
  classical
  rcases hlarge with ⟨x0, hx0⟩
  have h0 : (0 : ℕ) < d x0 := lt_of_lt_of_le (by decide : 0 < 2) hx0
  have h1 : (1 : ℕ) < d x0 := lt_of_lt_of_le (by decide : 1 < 2) hx0
  let a : Fin (d x0) := ⟨0, h0⟩
  let b : Fin (d x0) := ⟨1, h1⟩
  have hab : a ≠ b := by
    intro hab'
    have hval := congrArg Fin.val hab'
    simp [a, b] at hval
  let σ : Equiv.Perm (Fin (d x0)) := Equiv.swap a b
  have hσsign : Equiv.Perm.sign σ = -1 := by
    simpa [σ] using Equiv.Perm.sign_swap hab
  have hσsq : σ * σ = 1 := by
    ext z
    simp [σ]
  let e :
      {tau : FoldFiberNormalizer d // visibleProjection d tau = f ∧ foldFiberNormalizerSign d tau = 1}
        ≃
      {tau : FoldFiberNormalizer d //
          visibleProjection d tau = f ∧ foldFiberNormalizerSign d tau = -1} :=
    { toFun := by
        intro tau
        refine ⟨flipLift d x0 σ tau.1, ?_⟩
        constructor
        · simpa using tau.2.1
        · calc
            foldFiberNormalizerSign d (flipLift d x0 σ tau.1)
                = Equiv.Perm.sign σ * foldFiberNormalizerSign d tau.1 :=
                    foldFiberNormalizerSign_flipLift d x0 σ tau.1
            _ = -1 := by simp [hσsign, tau.2.2]
      invFun := by
        intro tau
        refine ⟨flipLift d x0 σ tau.1, ?_⟩
        constructor
        · simpa using tau.2.1
        · calc
            foldFiberNormalizerSign d (flipLift d x0 σ tau.1)
                = Equiv.Perm.sign σ * foldFiberNormalizerSign d tau.1 :=
                    foldFiberNormalizerSign_flipLift d x0 σ tau.1
            _ = 1 := by simp [hσsign, tau.2.2]
      left_inv := by
        intro tau
        apply Subtype.ext
        exact flipLift_involutive d x0 σ hσsq tau.1
      right_inv := by
        intro tau
        apply Subtype.ext
        exact flipLift_involutive d x0 σ hσsq tau.1 }
  exact Fintype.card_congr e

end Omega.OperatorAlgebra
