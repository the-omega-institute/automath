import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.OperatorAlgebra

section

variable {Ω X : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype X] [DecidableEq X]

namespace FoldJonesBasicConstructionDirectsum

/-- The fiber of `fold` over `x`. -/
def foldFiber (fold : Ω → X) (x : X) :=
  { ω : Ω // fold ω = x }

instance foldFiberDecidableEq (fold : Ω → X) (x : X) : DecidableEq (foldFiber fold x) :=
  show DecidableEq { ω : Ω // fold ω = x } from inferInstance

instance foldFiberFintype (fold : Ω → X) (x : X) : Fintype (foldFiber fold x) :=
  show Fintype { ω : Ω // fold ω = x } from inferInstance

/-- The standard matrix unit on the `x`-fiber block. -/
def fiberMatrixUnit (fold : Ω → X) (x : X)
    (ω ω' : foldFiber fold x) : Matrix (foldFiber fold x) (foldFiber fold x) ℂ :=
  Matrix.single ω ω' 1

/-- The ambient basis decomposes as a sigma-type of fold fibers. -/
def directsumMatrixDecomposition (fold : Ω → X) : Prop :=
  Nonempty (Ω ≃ Σ x : X, foldFiber fold x)

/-- On each fiber block, the canonical matrix units satisfy the expected multiplication and
adjoint laws. -/
def matrixUnitGeneration (fold : Ω → X) : Prop :=
  (∀ x (ω ω' η η' : foldFiber fold x),
      fiberMatrixUnit fold x ω ω' * fiberMatrixUnit fold x η η' =
        if ω' = η then fiberMatrixUnit fold x ω η' else 0) ∧
    ∀ x (ω ω' : foldFiber fold x),
      Matrix.conjTranspose (fiberMatrixUnit fold x ω ω') = fiberMatrixUnit fold x ω' ω

/-- The diagonal matrix units already sum to the identity on each fiber block, so the basic
construction closes after one matrix-block step. -/
def depthTwoClosure (fold : Ω → X) : Prop :=
  ∀ x, (∑ ω : foldFiber fold x, fiberMatrixUnit fold x ω ω) =
    (1 : Matrix (foldFiber fold x) (foldFiber fold x) ℂ)

def foldFiberEquivSigma (fold : Ω → X) : Ω ≃ Σ x : X, foldFiber fold x where
  toFun ω := ⟨fold ω, ⟨ω, rfl⟩⟩
  invFun s := s.2.1
  left_inv ω := rfl
  right_inv s := by
    rcases s with ⟨x, ⟨ω, hω⟩⟩
    cases hω
    rfl

omit [Fintype X] in
lemma fiberMatrixUnit_mul (fold : Ω → X) (x : X)
    (ω ω' η η' : foldFiber fold x) :
    fiberMatrixUnit fold x ω ω' * fiberMatrixUnit fold x η η' =
      if ω' = η then fiberMatrixUnit fold x ω η' else 0 := by
  by_cases h : ω' = η
  · subst h
    simp [fiberMatrixUnit]
  · simp [fiberMatrixUnit, h]

omit [Fintype Ω] [Fintype X] [DecidableEq X] in
lemma fiberMatrixUnit_conjTranspose (fold : Ω → X) (x : X)
    (ω ω' : foldFiber fold x) :
    Matrix.conjTranspose (fiberMatrixUnit fold x ω ω') = fiberMatrixUnit fold x ω' ω := by
  simp [fiberMatrixUnit]

omit [Fintype X] in
lemma sum_diagonal_fiberMatrixUnit (fold : Ω → X) (x : X) :
    (∑ ω : foldFiber fold x, fiberMatrixUnit fold x ω ω) =
      (1 : Matrix (foldFiber fold x) (foldFiber fold x) ℂ) := by
  ext i j
  rw [Matrix.one_apply, Fintype.sum_apply, Fintype.sum_apply]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single i]
    · simp [fiberMatrixUnit, Matrix.single]
    · intro b _ hbi
      simp [fiberMatrixUnit, Matrix.single, hbi]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  · rw [if_neg h]
    refine Finset.sum_eq_zero ?_
    intro b hb
    by_cases hbi : b = i
    · have hbj : b ≠ j := by
        intro hbj
        exact h (hbi.symm.trans hbj)
      have hij : i ≠ j := h
      simp [fiberMatrixUnit, Matrix.single, hbi, hij]
    · simp [fiberMatrixUnit, Matrix.single, hbi]

/-- Paper-facing finite-dimensional Jones basic construction package: the fold basis decomposes as
a direct sum of fiber blocks, each block carries canonical matrix units, and the diagonal matrix
units already recover the identity on that block.
    thm:fold-jones-basic-construction-directsum -/
theorem paper_op_algebra_fold_jones_basic_construction_directsum
    (fold : Ω → X) :
    directsumMatrixDecomposition fold ∧ matrixUnitGeneration fold ∧ depthTwoClosure fold := by
  refine ⟨?_, ?_⟩
  · exact ⟨foldFiberEquivSigma fold⟩
  · refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro x ω ω' η η'
        exact fiberMatrixUnit_mul fold x ω ω' η η'
      · intro x ω ω'
        exact fiberMatrixUnit_conjTranspose fold x ω ω'
    · intro x
      exact sum_diagonal_fiberMatrixUnit fold x

end FoldJonesBasicConstructionDirectsum

open FoldJonesBasicConstructionDirectsum

theorem paper_op_algebra_fold_jones_basic_construction_directsum
    (fold : Ω → X) :
    directsumMatrixDecomposition fold ∧ matrixUnitGeneration fold ∧ depthTwoClosure fold := by
  refine ⟨?_, ?_⟩
  · exact ⟨foldFiberEquivSigma fold⟩
  · refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro x ω ω' η η'
        exact fiberMatrixUnit_mul fold x ω ω' η η'
      · intro x ω ω'
        exact fiberMatrixUnit_conjTranspose fold x ω ω'
    · intro x
      exact sum_diagonal_fiberMatrixUnit fold x

end

end Omega.OperatorAlgebra
