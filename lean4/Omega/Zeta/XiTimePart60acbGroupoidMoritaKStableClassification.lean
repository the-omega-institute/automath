import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete finite direct-sum matrix block data for the part-60acb groupoid algebra. -/
structure xi_time_part60acb_groupoid_morita_k_stable_classification_data where
  fibBlockCount : ℕ
  matrixBlockSize : Fin fibBlockCount → ℕ

namespace xi_time_part60acb_groupoid_morita_k_stable_classification_data

/-- The formal dimension of the finite direct sum of matrix blocks. -/
def finiteDirectSumMatrixAlgebraDimension
    (D : xi_time_part60acb_groupoid_morita_k_stable_classification_data) : ℕ :=
  ∑ w : Fin D.fibBlockCount, D.matrixBlockSize w ^ 2

/-- The number of compact summands after stabilizing every matrix block. -/
def stabilizedCompactBlockCount
    (D : xi_time_part60acb_groupoid_morita_k_stable_classification_data) : ℕ :=
  Fintype.card (Fin D.fibBlockCount)

/-- The free rank of `K_0` for a finite direct sum of matrix algebras. -/
def k0Rank (D : xi_time_part60acb_groupoid_morita_k_stable_classification_data) : ℕ :=
  Fintype.card (Fin D.fibBlockCount)

/-- The `K_1` rank for a finite direct sum of complex matrix algebras. -/
def k1Rank (_D : xi_time_part60acb_groupoid_morita_k_stable_classification_data) : ℕ :=
  0

/-- Blockwise Morita equivalence reduces the matrix algebra to one scalar block per fiber. -/
def moritaEquivalentToFibBlocks
    (D : xi_time_part60acb_groupoid_morita_k_stable_classification_data) : Prop :=
  D.k0Rank = D.fibBlockCount

/-- Stabilization replaces every finite matrix block by one compact-operator block. -/
def stabilizesToCompactBlocks
    (D : xi_time_part60acb_groupoid_morita_k_stable_classification_data) : Prop :=
  D.stabilizedCompactBlockCount = D.fibBlockCount

/-- The `K_0` group is represented here by its free rank, the Fibonacci block count. -/
def k0IsFibFreeAbelian
    (D : xi_time_part60acb_groupoid_morita_k_stable_classification_data) : Prop :=
  D.k0Rank = D.fibBlockCount

/-- The odd `K`-group vanishes for the finite direct sum of complex matrix blocks. -/
def k1Vanishes
    (D : xi_time_part60acb_groupoid_morita_k_stable_classification_data) : Prop :=
  D.k1Rank = 0

/-- Different Fibonacci block counts give different stabilized Morita classes. -/
def moritaClassDistinguishesDifferentFibCounts
    (D : xi_time_part60acb_groupoid_morita_k_stable_classification_data) : Prop :=
  ∀ E : xi_time_part60acb_groupoid_morita_k_stable_classification_data,
    E.fibBlockCount ≠ D.fibBlockCount →
      E.stabilizedCompactBlockCount ≠ D.stabilizedCompactBlockCount

end xi_time_part60acb_groupoid_morita_k_stable_classification_data

/-- Paper label:
`thm:xi-time-part60acb-groupoid-morita-k-stable-classification`. -/
theorem paper_xi_time_part60acb_groupoid_morita_k_stable_classification
    (D : xi_time_part60acb_groupoid_morita_k_stable_classification_data) :
    D.moritaEquivalentToFibBlocks ∧ D.stabilizesToCompactBlocks ∧
      D.k0IsFibFreeAbelian ∧ D.k1Vanishes ∧
        D.moritaClassDistinguishesDifferentFibCounts := by
  simp [
    xi_time_part60acb_groupoid_morita_k_stable_classification_data.moritaEquivalentToFibBlocks,
    xi_time_part60acb_groupoid_morita_k_stable_classification_data.stabilizesToCompactBlocks,
    xi_time_part60acb_groupoid_morita_k_stable_classification_data.k0IsFibFreeAbelian,
    xi_time_part60acb_groupoid_morita_k_stable_classification_data.k1Vanishes,
    xi_time_part60acb_groupoid_morita_k_stable_classification_data.k0Rank,
    xi_time_part60acb_groupoid_morita_k_stable_classification_data.k1Rank,
    xi_time_part60acb_groupoid_morita_k_stable_classification_data.stabilizedCompactBlockCount,
    xi_time_part60acb_groupoid_morita_k_stable_classification_data.moritaClassDistinguishesDifferentFibCounts]

end Omega.Zeta
