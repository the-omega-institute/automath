import Mathlib

namespace Omega.CircleDimension

/-- The `2 × 2` Pascal block obtained after factoring the powers of `2` from the odd-odd Gram
closed form. -/
def kernelOddPascalMatrix : Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j => if i.1 ≤ j.1 then (Nat.choose j.1 i.1 : ℤ) else 0

/-- The concrete odd-odd Gram block before removing the dyadic scaling. -/
def kernelOddGramMatrix : Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j => (2 : ℤ) * kernelOddPascalMatrix i j

/-- Natural determinant attached to the concrete odd-odd Gram block. -/
def kernelOddGramDetNat : Nat :=
  Int.natAbs (Matrix.det kernelOddGramMatrix)

/-- The dyadic valuation extracted from the determinant. -/
def kernelOddGramV2 : Nat :=
  Nat.factorization kernelOddGramDetNat 2

private lemma kernelOddPascal_det : Matrix.det kernelOddPascalMatrix = 1 := by
  norm_num [kernelOddPascalMatrix, Matrix.det_fin_two]

private lemma kernelOddGram_det : Matrix.det kernelOddGramMatrix = 4 := by
  norm_num [kernelOddGramMatrix, kernelOddPascalMatrix, Matrix.det_fin_two]

/-- For the first nontrivial odd-odd Gram block, removing the dyadic scaling leaves the Pascal
matrix `[[1, 1], [0, 1]]`, whose determinant is `1` and hence odd. Restoring the extracted
`2`-factors gives determinant `4`, so the exact `v₂` is `2`.
    prop:cdim-kernel-odd-gram-v2-determinant -/
theorem paper_cdim_kernel_odd_gram_v2_determinant :
    Matrix.det kernelOddPascalMatrix = 1 ∧
      Odd (Int.natAbs (Matrix.det kernelOddPascalMatrix)) ∧
      Matrix.det kernelOddGramMatrix = 4 ∧
      kernelOddGramDetNat = 4 ∧
      kernelOddGramV2 = 2 := by
  refine ⟨kernelOddPascal_det, by simp [kernelOddPascal_det], kernelOddGram_det,
    by simp [kernelOddGramDetNat, kernelOddGram_det], ?_⟩
  simpa [kernelOddGramV2, kernelOddGramDetNat, kernelOddGram_det] using
    (show Nat.factorization 4 2 = 2 by native_decide)

end Omega.CircleDimension
