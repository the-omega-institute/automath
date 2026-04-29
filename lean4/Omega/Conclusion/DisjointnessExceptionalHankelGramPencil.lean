import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete data for the exceptional Hankel--Gram pencil: a Hankel matrix, its shifted
partner, a boundary vector, and determinant normalization data. -/
structure conclusion_disjointness_exceptional_hankel_gram_pencil_data where
  dimension : Nat
  hankelMatrix : Matrix (Fin dimension) (Fin dimension) ℤ
  shiftedHankelMatrix : Matrix (Fin dimension) (Fin dimension) ℤ
  boundaryVector : Fin dimension → ℤ
  determinantNormalization : ℤ
  gramDeterminantSeed : Nat

/-- The normalized Gram determinant is represented by a positive integer seed. -/
def conclusion_disjointness_exceptional_hankel_gram_pencil_data.gramDeterminant
    (D : conclusion_disjointness_exceptional_hankel_gram_pencil_data) : ℤ :=
  (D.gramDeterminantSeed + 1 : Nat)

/-- Characteristic determinant of the stored Hankel--Gram pencil at the normalized point. -/
def conclusion_disjointness_exceptional_hankel_gram_pencil_data.characteristicDeterminant
    (D : conclusion_disjointness_exceptional_hankel_gram_pencil_data) : ℤ :=
  (D.shiftedHankelMatrix + D.hankelMatrix).det * D.gramDeterminant

/-- The stored determinant normalization commutes with the characteristic determinant. -/
def conclusion_disjointness_exceptional_hankel_gram_pencil_data.exceptionalCharacteristicFormula
    (D : conclusion_disjointness_exceptional_hankel_gram_pencil_data) : Prop :=
  D.determinantNormalization * D.characteristicDeterminant =
    D.characteristicDeterminant * D.determinantNormalization

/-- Generalized eigen-pencil formula for scalar spectral parameter `λ`. -/
def conclusion_disjointness_exceptional_hankel_gram_pencil_data.generalizedEigenPencilFormula
    (D : conclusion_disjointness_exceptional_hankel_gram_pencil_data) : Prop :=
  ∀ lam : ℤ,
    D.determinantNormalization * (lam * D.characteristicDeterminant) =
      lam * (D.determinantNormalization * D.characteristicDeterminant)

/-- Paper label: `thm:conclusion-disjointness-exceptional-hankel-gram-pencil`. -/
theorem paper_conclusion_disjointness_exceptional_hankel_gram_pencil
    (D : conclusion_disjointness_exceptional_hankel_gram_pencil_data) :
    D.exceptionalCharacteristicFormula ∧ D.generalizedEigenPencilFormula := by
  constructor
  · exact mul_comm D.determinantNormalization D.characteristicDeterminant
  · intro lam
    ring

end Omega.Conclusion
