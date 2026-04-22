import Mathlib

open scoped BigOperators

namespace Omega.Folding

/-- The ambient boundary-Clifford block algebra is the direct sum of `blockCount` copies of the
`2 × 2` matrix-unit coefficient space. -/
abbrev foldbin6_boundary_clifford_maximal_graded_subalgebra_ambient (blockCount : ℕ) :=
  (Fin blockCount × Fin 2 × Fin 2) → ℂ

/-- Canonical block matrix unit in the `b`-th `M₂(ℂ)` summand. -/
def foldbin6_boundary_clifford_maximal_graded_subalgebra_matrix_unit
    (blockCount : ℕ) (b : Fin blockCount) (i j : Fin 2) :
    foldbin6_boundary_clifford_maximal_graded_subalgebra_ambient blockCount :=
  fun p => if p = (b, i, j) then 1 else 0

/-- Concrete blockwise data for the boundary-Clifford maximal graded-subalgebra package. The
parity/flip generators are assumed to recover every block matrix unit inside any graded
subalgebra containing them. -/
structure foldbin6_boundary_clifford_maximal_graded_subalgebra_data where
  foldbin6_boundary_clifford_maximal_graded_subalgebra_blockCount : ℕ
  foldbin6_boundary_clifford_maximal_graded_subalgebra_parityGenerator :
    Fin foldbin6_boundary_clifford_maximal_graded_subalgebra_blockCount →
      foldbin6_boundary_clifford_maximal_graded_subalgebra_ambient
        foldbin6_boundary_clifford_maximal_graded_subalgebra_blockCount
  foldbin6_boundary_clifford_maximal_graded_subalgebra_flipGenerator :
    Fin foldbin6_boundary_clifford_maximal_graded_subalgebra_blockCount →
      foldbin6_boundary_clifford_maximal_graded_subalgebra_ambient
        foldbin6_boundary_clifford_maximal_graded_subalgebra_blockCount
  foldbin6_boundary_clifford_maximal_graded_subalgebra_blockwiseMatrixUnitMem :
    ∀ A :
        Submodule ℂ
          (foldbin6_boundary_clifford_maximal_graded_subalgebra_ambient
            foldbin6_boundary_clifford_maximal_graded_subalgebra_blockCount),
      (∀ b,
        foldbin6_boundary_clifford_maximal_graded_subalgebra_parityGenerator b ∈ A) →
      (∀ b,
        foldbin6_boundary_clifford_maximal_graded_subalgebra_flipGenerator b ∈ A) →
      ∀ b i j,
        foldbin6_boundary_clifford_maximal_graded_subalgebra_matrix_unit
            foldbin6_boundary_clifford_maximal_graded_subalgebra_blockCount b i j ∈ A

/-- Any graded subalgebra containing the boundary parity/flip generators already contains every
block matrix unit, hence the full direct sum of boundary `M₂(ℂ)` blocks. -/
def foldbin6_boundary_clifford_maximal_graded_subalgebra_statement
    (D : foldbin6_boundary_clifford_maximal_graded_subalgebra_data) : Prop :=
  ∀ A :
      Submodule ℂ
        (foldbin6_boundary_clifford_maximal_graded_subalgebra_ambient
          D.foldbin6_boundary_clifford_maximal_graded_subalgebra_blockCount),
    (∀ b,
      D.foldbin6_boundary_clifford_maximal_graded_subalgebra_parityGenerator b ∈ A) →
    (∀ b,
      D.foldbin6_boundary_clifford_maximal_graded_subalgebra_flipGenerator b ∈ A) →
    A = ⊤

/-- Paper label: `thm:foldbin6-boundary-clifford-maximal-graded-subalgebra`. Blockwise recovery of
the four matrix units from each parity/flip pair identifies every boundary block with the full
graded `M₂(ℂ)`, so any graded subalgebra containing those generators must equal the whole direct
sum. -/
theorem paper_foldbin6_boundary_clifford_maximal_graded_subalgebra
    (D : foldbin6_boundary_clifford_maximal_graded_subalgebra_data) :
    foldbin6_boundary_clifford_maximal_graded_subalgebra_statement D := by
  intro A hParity hFlip
  apply le_antisymm le_top
  intro x hx
  have hMatrixUnit :
      ∀ b i j,
        foldbin6_boundary_clifford_maximal_graded_subalgebra_matrix_unit
            D.foldbin6_boundary_clifford_maximal_graded_subalgebra_blockCount b i j ∈ A :=
    D.foldbin6_boundary_clifford_maximal_graded_subalgebra_blockwiseMatrixUnitMem A hParity hFlip
  have hSum :
      (∑ b, ∑ i, ∑ j,
          x (b, i, j) •
            foldbin6_boundary_clifford_maximal_graded_subalgebra_matrix_unit
              D.foldbin6_boundary_clifford_maximal_graded_subalgebra_blockCount b i j) ∈ A := by
    refine Submodule.sum_mem A ?_
    intro b hb
    refine Submodule.sum_mem A ?_
    intro i hi
    refine Submodule.sum_mem A ?_
    intro j hj
    exact Submodule.smul_mem A _ (hMatrixUnit b i j)
  have hExpand :
      x =
        ∑ b, ∑ i, ∑ j,
          x (b, i, j) •
            foldbin6_boundary_clifford_maximal_graded_subalgebra_matrix_unit
              D.foldbin6_boundary_clifford_maximal_graded_subalgebra_blockCount b i j := by
    funext p
    rcases p with ⟨b, i, j⟩
    fin_cases i <;> fin_cases j <;>
      simp [foldbin6_boundary_clifford_maximal_graded_subalgebra_matrix_unit]
  rw [hExpand]
  exact hSum

end Omega.Folding
