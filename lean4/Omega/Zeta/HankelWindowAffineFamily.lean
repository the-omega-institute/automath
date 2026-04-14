import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix

variable {k : Type*} [CommRing k]

/-- Decomposing `Function.update b j x` as the zero-pinned vector plus a rank-1
    update `x • Pi.single j 1`.
    prop:xi-hankel-window-affine-family -/
theorem update_eq_add_smul_single
    {α : Type*} [DecidableEq α]
    (b : α → k) (j : α) (x : k) :
    Function.update b j x =
      Function.update b j 0 + x • (Pi.single j 1 : α → k) := by
  funext i
  by_cases hi : i = j
  · subst hi
    simp
  · simp [Function.update_of_ne hi, Pi.single_eq_of_ne hi]

/-- Matrix-vector multiplication is affine in the `j`-th slot of the input vector.
    prop:xi-hankel-window-affine-family -/
theorem mulVec_update_affine
    {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α k) (b : α → k) (j : α) (x : k) :
    A *ᵥ (Function.update b j x) =
      A *ᵥ (Function.update b j 0) + x • A *ᵥ (Pi.single j 1) := by
  rw [update_eq_add_smul_single b j x, Matrix.mulVec_add, Matrix.mulVec_smul]

/-- Paper package: Hankel window affine family structure.
    prop:xi-hankel-window-affine-family -/
theorem paper_xi_hankel_window_affine_family
    {α : Type*} [Fintype α] [DecidableEq α] :
    (∀ (b : α → k) (j : α) (x : k),
      Function.update b j x = Function.update b j 0 + x • (Pi.single j 1 : α → k)) ∧
    (∀ (A : Matrix α α k) (b : α → k) (j : α) (x : k),
      A *ᵥ (Function.update b j x) =
        A *ᵥ (Function.update b j 0) + x • A *ᵥ (Pi.single j 1)) ∧
    (∀ (A : Matrix α α k) (b : α → k) (j : α),
      ∃ c₀ v : α → k, ∀ x : k,
        A *ᵥ (Function.update b j x) = c₀ + x • v) := by
  refine ⟨update_eq_add_smul_single, mulVec_update_affine, ?_⟩
  intro A b j
  refine ⟨A *ᵥ Function.update b j 0, A *ᵥ Pi.single j 1, ?_⟩
  intro x
  exact mulVec_update_affine A b j x

end Omega.Zeta
