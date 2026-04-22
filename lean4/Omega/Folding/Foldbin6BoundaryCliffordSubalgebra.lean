import Mathlib
import Omega.Folding.Foldbin6BoundaryCliffordMaximalGradedSubalgebra

namespace Omega.Folding

/-- The direct sum of the boundary `M₂(ℂ)` coefficient spaces. -/
abbrev foldbin6_boundary_clifford_subalgebra_ambient (blockCount : ℕ) :=
  foldbin6_boundary_clifford_maximal_graded_subalgebra_ambient blockCount

/-- Block-supported identity in the `b`-th `M₂(ℂ)` summand. -/
def foldbin6_boundary_clifford_subalgebra_block_id (blockCount : ℕ) (b : Fin blockCount) :
    foldbin6_boundary_clifford_subalgebra_ambient blockCount :=
  foldbin6_boundary_clifford_maximal_graded_subalgebra_matrix_unit blockCount b 0 0 +
    foldbin6_boundary_clifford_maximal_graded_subalgebra_matrix_unit blockCount b 1 1

/-- Boundary parity generator `diag(1,-1)` in the `b`-th block. -/
def foldbin6_boundary_clifford_subalgebra_parity_generator
    (blockCount : ℕ) (b : Fin blockCount) :
    foldbin6_boundary_clifford_subalgebra_ambient blockCount :=
  foldbin6_boundary_clifford_maximal_graded_subalgebra_matrix_unit blockCount b 0 0 -
    foldbin6_boundary_clifford_maximal_graded_subalgebra_matrix_unit blockCount b 1 1

/-- Boundary flip generator `[[0,1],[1,0]]` in the `b`-th block. -/
def foldbin6_boundary_clifford_subalgebra_flip_generator
    (blockCount : ℕ) (b : Fin blockCount) :
    foldbin6_boundary_clifford_subalgebra_ambient blockCount :=
  foldbin6_boundary_clifford_maximal_graded_subalgebra_matrix_unit blockCount b 0 1 +
    foldbin6_boundary_clifford_maximal_graded_subalgebra_matrix_unit blockCount b 1 0

/-- Pointwise block multiplication inside the direct sum of `M₂(ℂ)` blocks. -/
noncomputable def foldbin6_boundary_clifford_subalgebra_block_mul {blockCount : ℕ}
    (x y : foldbin6_boundary_clifford_subalgebra_ambient blockCount) :
    foldbin6_boundary_clifford_subalgebra_ambient blockCount :=
  fun p => ∑ k : Fin 2, x (p.1, p.2.1, k) * y (p.1, k, p.2.2)

/-- Concrete boundary-Clifford package: any submodule containing the parity and flip generators
recovers every block matrix unit. -/
structure foldbin6_boundary_clifford_subalgebra_data where
  blockCount : ℕ
  blockwiseMatrixUnitMem :
    ∀ A : Submodule ℂ (foldbin6_boundary_clifford_subalgebra_ambient blockCount),
      (∀ b, foldbin6_boundary_clifford_subalgebra_parity_generator blockCount b ∈ A) →
      (∀ b, foldbin6_boundary_clifford_subalgebra_flip_generator blockCount b ∈ A) →
      ∀ b i j,
        foldbin6_boundary_clifford_maximal_graded_subalgebra_matrix_unit blockCount b i j ∈ A

private lemma foldbin6_boundary_clifford_subalgebra_parity_sq (blockCount : ℕ)
    (b : Fin blockCount) :
    foldbin6_boundary_clifford_subalgebra_block_mul
        (foldbin6_boundary_clifford_subalgebra_parity_generator blockCount b)
        (foldbin6_boundary_clifford_subalgebra_parity_generator blockCount b) =
      foldbin6_boundary_clifford_subalgebra_block_id blockCount b := by
  ext p
  rcases p with ⟨b', i, j⟩
  by_cases hb : b' = b
  · subst hb
    fin_cases i <;> fin_cases j <;>
      simp [foldbin6_boundary_clifford_subalgebra_block_mul,
        foldbin6_boundary_clifford_subalgebra_parity_generator,
        foldbin6_boundary_clifford_subalgebra_block_id,
        foldbin6_boundary_clifford_maximal_graded_subalgebra_matrix_unit]
  · fin_cases i <;> fin_cases j <;>
      simp [foldbin6_boundary_clifford_subalgebra_block_mul,
        foldbin6_boundary_clifford_subalgebra_parity_generator,
        foldbin6_boundary_clifford_subalgebra_block_id,
        foldbin6_boundary_clifford_maximal_graded_subalgebra_matrix_unit, hb]

private lemma foldbin6_boundary_clifford_subalgebra_flip_sq (blockCount : ℕ) (b : Fin blockCount) :
    foldbin6_boundary_clifford_subalgebra_block_mul
        (foldbin6_boundary_clifford_subalgebra_flip_generator blockCount b)
        (foldbin6_boundary_clifford_subalgebra_flip_generator blockCount b) =
      foldbin6_boundary_clifford_subalgebra_block_id blockCount b := by
  ext p
  rcases p with ⟨b', i, j⟩
  by_cases hb : b' = b
  · subst hb
    fin_cases i <;> fin_cases j <;>
      simp [foldbin6_boundary_clifford_subalgebra_block_mul,
        foldbin6_boundary_clifford_subalgebra_flip_generator,
        foldbin6_boundary_clifford_subalgebra_block_id,
        foldbin6_boundary_clifford_maximal_graded_subalgebra_matrix_unit]
  · fin_cases i <;> fin_cases j <;>
      simp [foldbin6_boundary_clifford_subalgebra_block_mul,
        foldbin6_boundary_clifford_subalgebra_flip_generator,
        foldbin6_boundary_clifford_subalgebra_block_id,
        foldbin6_boundary_clifford_maximal_graded_subalgebra_matrix_unit, hb]

private lemma foldbin6_boundary_clifford_subalgebra_parity_flip_anticomm
    (blockCount : ℕ) (b : Fin blockCount) :
    foldbin6_boundary_clifford_subalgebra_block_mul
        (foldbin6_boundary_clifford_subalgebra_parity_generator blockCount b)
        (foldbin6_boundary_clifford_subalgebra_flip_generator blockCount b) =
      -foldbin6_boundary_clifford_subalgebra_block_mul
        (foldbin6_boundary_clifford_subalgebra_flip_generator blockCount b)
        (foldbin6_boundary_clifford_subalgebra_parity_generator blockCount b) := by
  ext p
  rcases p with ⟨b', i, j⟩
  by_cases hb : b' = b
  · subst hb
    fin_cases i <;> fin_cases j <;>
      simp [foldbin6_boundary_clifford_subalgebra_block_mul,
        foldbin6_boundary_clifford_subalgebra_parity_generator,
        foldbin6_boundary_clifford_subalgebra_flip_generator,
        foldbin6_boundary_clifford_maximal_graded_subalgebra_matrix_unit]
  · fin_cases i <;> fin_cases j <;>
      simp [foldbin6_boundary_clifford_subalgebra_block_mul,
        foldbin6_boundary_clifford_subalgebra_parity_generator,
        foldbin6_boundary_clifford_subalgebra_flip_generator,
        foldbin6_boundary_clifford_maximal_graded_subalgebra_matrix_unit, hb]

/-- The boundary parity/flip generators satisfy the blockwise Clifford relations and any submodule
containing all of them is already the full direct sum of boundary `M₂(ℂ)` blocks. -/
def foldbin6_boundary_clifford_subalgebra_statement
    (D : foldbin6_boundary_clifford_subalgebra_data) : Prop :=
  (∀ b,
    foldbin6_boundary_clifford_subalgebra_block_mul
        (foldbin6_boundary_clifford_subalgebra_parity_generator D.blockCount b)
        (foldbin6_boundary_clifford_subalgebra_parity_generator D.blockCount b) =
      foldbin6_boundary_clifford_subalgebra_block_id D.blockCount b ∧
      foldbin6_boundary_clifford_subalgebra_block_mul
          (foldbin6_boundary_clifford_subalgebra_flip_generator D.blockCount b)
          (foldbin6_boundary_clifford_subalgebra_flip_generator D.blockCount b) =
        foldbin6_boundary_clifford_subalgebra_block_id D.blockCount b ∧
      foldbin6_boundary_clifford_subalgebra_block_mul
          (foldbin6_boundary_clifford_subalgebra_parity_generator D.blockCount b)
          (foldbin6_boundary_clifford_subalgebra_flip_generator D.blockCount b) =
        -foldbin6_boundary_clifford_subalgebra_block_mul
          (foldbin6_boundary_clifford_subalgebra_flip_generator D.blockCount b)
          (foldbin6_boundary_clifford_subalgebra_parity_generator D.blockCount b)) ∧
    ∀ A : Submodule ℂ (foldbin6_boundary_clifford_subalgebra_ambient D.blockCount),
      (∀ b, foldbin6_boundary_clifford_subalgebra_parity_generator D.blockCount b ∈ A) →
      (∀ b, foldbin6_boundary_clifford_subalgebra_flip_generator D.blockCount b ∈ A) →
      A = ⊤

/-- Paper label: `prop:foldbin6-boundary-clifford-subalgebra`. On each boundary block the parity
and flip generators satisfy the Pauli/Clifford relations `P² = X² = I` and `PX = -XP`; the
existing maximal-graded theorem then upgrades the blockwise recovery of matrix units to the full
direct sum of boundary `M₂(ℂ)` blocks. -/
theorem paper_foldbin6_boundary_clifford_subalgebra (D : foldbin6_boundary_clifford_subalgebra_data) :
    foldbin6_boundary_clifford_subalgebra_statement D := by
  refine ⟨?_, ?_⟩
  · intro b
    exact ⟨foldbin6_boundary_clifford_subalgebra_parity_sq D.blockCount b,
      foldbin6_boundary_clifford_subalgebra_flip_sq D.blockCount b,
      foldbin6_boundary_clifford_subalgebra_parity_flip_anticomm D.blockCount b⟩
  · intro A hParity hFlip
    let Dmax : foldbin6_boundary_clifford_maximal_graded_subalgebra_data :=
      { foldbin6_boundary_clifford_maximal_graded_subalgebra_blockCount := D.blockCount
        foldbin6_boundary_clifford_maximal_graded_subalgebra_parityGenerator :=
          foldbin6_boundary_clifford_subalgebra_parity_generator D.blockCount
        foldbin6_boundary_clifford_maximal_graded_subalgebra_flipGenerator :=
          foldbin6_boundary_clifford_subalgebra_flip_generator D.blockCount
        foldbin6_boundary_clifford_maximal_graded_subalgebra_blockwiseMatrixUnitMem :=
          D.blockwiseMatrixUnitMem }
    simpa [foldbin6_boundary_clifford_subalgebra_ambient] using
      (paper_foldbin6_boundary_clifford_maximal_graded_subalgebra Dmax) A hParity hFlip

end Omega.Folding
