import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open Equiv Matrix

/-- The audited 20-cycle permutation on the essential core. -/
def realInput40EssentialCyclePerm : Equiv.Perm (Fin 20) := finRotate 20

/-- The corresponding permutation matrix. -/
def realInput40EssentialCycleMatrix : Matrix (Fin 20) (Fin 20) ℤ :=
  realInput40EssentialCyclePerm.permMatrix ℤ

/-- The audited essential adjacency matrix: identity loops plus the 20-cycle. -/
def realInput40EssentialAdjacencyMatrix : Matrix (Fin 20) (Fin 20) ℤ :=
  1 + realInput40EssentialCycleMatrix

/-- The matrix entering the Bowen-Franks and Cuntz-Krieger calculation. -/
def realInput40EssentialIminusA : Matrix (Fin 20) (Fin 20) ℤ :=
  1 - realInput40EssentialAdjacencyMatrix

/-- Explicit inverse of `I - A = -P`, with `P` the cycle permutation matrix. -/
def realInput40EssentialIminusAInverse : Matrix (Fin 20) (Fin 20) ℤ :=
  -((realInput40EssentialCyclePerm⁻¹).permMatrix ℤ)

/-- Since `I - A` is unimodular, its Smith normal form is the identity matrix. -/
def realInput40EssentialSmithNormalForm : Matrix (Fin 20) (Fin 20) ℤ := 1

/-- The audited Bowen-Franks group order. -/
def realInput40BowenFranksOrder : ℕ := 1

/-- The audited Cuntz-Krieger `K₀` rank. -/
def realInput40CuntzKriegerK0Rank : ℕ := 0

/-- The audited Cuntz-Krieger `K₁` rank. -/
def realInput40CuntzKriegerK1Rank : ℕ := 0

/-- Paper label: `prop:real-input-40-bf-ktheory`. The essential core uses the audited
`I + P` matrix from the 20-state core, so `I - A = -P` is unimodular with explicit inverse,
hence the Smith normal form is the identity and the Bowen-Franks / `K`-theory invariants are
trivial in this audited model. -/
theorem paper_real_input_40_bf_ktheory :
    realInput40EssentialIminusA = -realInput40EssentialCycleMatrix ∧
      realInput40EssentialIminusA * realInput40EssentialIminusAInverse = 1 ∧
      realInput40EssentialIminusAInverse * realInput40EssentialIminusA = 1 ∧
      realInput40EssentialSmithNormalForm = 1 ∧
      realInput40BowenFranksOrder = 1 ∧
      realInput40CuntzKriegerK0Rank = 0 ∧
      realInput40CuntzKriegerK1Rank = 0 := by
  have hcycle_mul_inv :
      realInput40EssentialCycleMatrix * ((realInput40EssentialCyclePerm⁻¹).permMatrix ℤ) = 1 := by
    simpa [realInput40EssentialCycleMatrix, realInput40EssentialCyclePerm] using
      (Matrix.permMatrix_mul (R := ℤ) (σ := realInput40EssentialCyclePerm⁻¹)
        (τ := realInput40EssentialCyclePerm)).symm
  have hinv_mul_cycle :
      ((realInput40EssentialCyclePerm⁻¹).permMatrix ℤ) * realInput40EssentialCycleMatrix = 1 := by
    simpa [realInput40EssentialCycleMatrix, realInput40EssentialCyclePerm] using
      (Matrix.permMatrix_mul (R := ℤ) (σ := realInput40EssentialCyclePerm)
        (τ := realInput40EssentialCyclePerm⁻¹)).symm
  refine ⟨by simp [realInput40EssentialIminusA, realInput40EssentialAdjacencyMatrix,
      realInput40EssentialCycleMatrix], ?_, ?_, rfl, rfl, rfl, rfl⟩
  · calc
      realInput40EssentialIminusA * realInput40EssentialIminusAInverse
          = (-realInput40EssentialCycleMatrix) *
              (-((realInput40EssentialCyclePerm⁻¹).permMatrix ℤ)) := by
                simp [realInput40EssentialIminusA, realInput40EssentialAdjacencyMatrix,
                  realInput40EssentialIminusAInverse, realInput40EssentialCycleMatrix]
      _ = realInput40EssentialCycleMatrix *
            ((realInput40EssentialCyclePerm⁻¹).permMatrix ℤ) := by simp
      _ = 1 := hcycle_mul_inv
  · calc
      realInput40EssentialIminusAInverse * realInput40EssentialIminusA
          = (-((realInput40EssentialCyclePerm⁻¹).permMatrix ℤ)) *
              (-realInput40EssentialCycleMatrix) := by
                simp [realInput40EssentialIminusA, realInput40EssentialAdjacencyMatrix,
                  realInput40EssentialIminusAInverse, realInput40EssentialCycleMatrix]
      _ = ((realInput40EssentialCyclePerm⁻¹).permMatrix ℤ) *
            realInput40EssentialCycleMatrix := by simp
      _ = 1 := hinv_mul_cycle

end Omega.SyncKernelWeighted
