import Mathlib.Data.Complex.Basic
import Omega.Folding.StableSyntax

namespace Omega.Folding

noncomputable section

private def stableWordFibonacciSplitEquiv (m : ℕ) :
    Omega.X (m + 2) ≃ (Omega.X (m + 1) ⊕ Omega.X m) :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_sum, Omega.X.card_recurrence])

private def arrowCongrLeft (e : α ≃ β) : (α → γ) ≃ (β → γ) where
  toFun f := fun b => f (e.symm b)
  invFun g := fun a => g (e a)
  left_inv f := by
    funext a
    simp
  right_inv g := by
    funext b
    simp

private def sumArrowEquivProdArrow (α β γ : Type*) : (α ⊕ β → γ) ≃ ((α → γ) × (β → γ)) where
  toFun f := (fun a => f (.inl a), fun b => f (.inr b))
  invFun g
    | .inl a => g.1 a
    | .inr b => g.2 b
  left_inv f := by
    funext s
    cases s <;> rfl
  right_inv g := by
    cases g
    rfl

/-- Paper label: `cor:fold-stable-type-coordinate-algebra-fibonacci-splitting`. Lean requires a
`def` here because equivalences live in `Type`, not `Prop`. -/
noncomputable def paper_fold_stable_type_coordinate_algebra_fibonacci_splitting (m : ℕ) :
    (Omega.X (m + 2) → ℂ) ≃ ((Omega.X (m + 1) → ℂ) × (Omega.X m → ℂ)) := by
  exact
    (arrowCongrLeft (stableWordFibonacciSplitEquiv m)).trans
      (sumArrowEquivProdArrow (Omega.X (m + 1)) (Omega.X m) ℂ)

end

end Omega.Folding
