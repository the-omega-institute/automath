import Mathlib.Data.Fin.Basic

namespace Omega.OperatorAlgebra

/-- A finite fold model together with a permutation that preserves the fold equivalence relation. -/
structure FoldGroupoidMatrixUnitAutNormalizerData where
  n : ℕ
  perm : Equiv (Fin n) (Fin n)
  foldRel : Fin n → Fin n → Prop
  foldRel_refl : Reflexive foldRel
  foldRel_symm : Symmetric foldRel
  foldRel_trans : Transitive foldRel
  foldRel_perm : ∀ i j, foldRel i j ↔ foldRel (perm i) (perm j)

/-- The induced image of a matrix unit under the permutation. -/
def FoldGroupoidMatrixUnitAutNormalizerData.matrixUnitImage
    (D : FoldGroupoidMatrixUnitAutNormalizerData) (i j : Fin D.n) : Fin D.n × Fin D.n :=
  (D.perm i, D.perm j)

/-- The permutation recovered from the images of diagonal matrix units. -/
def FoldGroupoidMatrixUnitAutNormalizerData.recoveredPermutation
    (D : FoldGroupoidMatrixUnitAutNormalizerData) : Fin D.n → Fin D.n :=
  fun i => (D.matrixUnitImage i i).1

/-- The forward map preserves the fold relation on matrix-unit indices. -/
def FoldGroupoidMatrixUnitAutNormalizerData.forwardMapWellDefined
    (D : FoldGroupoidMatrixUnitAutNormalizerData) : Prop :=
  ∀ i j, D.foldRel i j → D.foldRel (D.matrixUnitImage i j).1 (D.matrixUnitImage i j).2

/-- Recovering the permutation from diagonal matrix units gives back the original permutation. -/
def FoldGroupoidMatrixUnitAutNormalizerData.inverseMapWellDefined
    (D : FoldGroupoidMatrixUnitAutNormalizerData) : Prop :=
  ∀ i, D.recoveredPermutation i = D.perm i

/-- The recovered permutation still preserves the fold equivalence relation. -/
def FoldGroupoidMatrixUnitAutNormalizerData.normalizerEquivMatrixUnitAut
    (D : FoldGroupoidMatrixUnitAutNormalizerData) : Prop :=
  ∀ i j, D.foldRel i j ↔ D.foldRel (D.recoveredPermutation i) (D.recoveredPermutation j)

/-- Paper wrapper: a fold-compatible permutation induces a well-defined matrix-unit action, the
diagonal matrix units recover the same permutation, and the recovered permutation still preserves
the fold relation.
    thm:op-algebra-fold-groupoid-matrix-unit-aut-normalizer -/
theorem paper_op_algebra_fold_groupoid_matrix_unit_aut_normalizer
    (D : FoldGroupoidMatrixUnitAutNormalizerData) :
    D.forwardMapWellDefined ∧ D.inverseMapWellDefined ∧ D.normalizerEquivMatrixUnitAut := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    simpa [FoldGroupoidMatrixUnitAutNormalizerData.matrixUnitImage] using
      (D.foldRel_perm i j).mp hij
  · intro i
    rfl
  · intro i j
    simpa [FoldGroupoidMatrixUnitAutNormalizerData.recoveredPermutation,
      FoldGroupoidMatrixUnitAutNormalizerData.matrixUnitImage] using D.foldRel_perm i j

end Omega.OperatorAlgebra
