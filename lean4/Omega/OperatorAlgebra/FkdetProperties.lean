import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

namespace Omega.OperatorAlgebra

open Matrix

noncomputable section

/-- Chapter-local audited raw determinant package: the absolute value of the matrix determinant. -/
def fkDetRaw {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ‖Matrix.det X‖

/-- Matrix-specialized normalized Fuglede--Kadison determinant. -/
def fkDetMatrixSpecialization {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ‖Matrix.det X‖ ^ (1 / (n : ℝ))

/-- Strict multiplicativity of the audited raw determinant package. -/
def strictMultiplicativity {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  fkDetRaw (X * Y) = fkDetRaw X * fkDetRaw Y

/-- Specialization to the normalized matrix trace formula `|det(X)|^(1/n)`. -/
def matrixSpecialization {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  fkDetMatrixSpecialization X = ‖Matrix.det X‖ ^ (1 / (n : ℝ))

/-- Vanishing of the determinant package is equivalent to noninvertibility of `I - K`. -/
def resonanceCriterion {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  fkDetRaw (1 - K) = 0 ↔ ¬ IsUnit (1 - K)

/-- For matrices, the audited determinant package is multiplicative, its normalized specialization
is exactly `|det(X)|^(1/n)`, and vanishing at `I - K` is the same as noninvertibility. -/
theorem paper_op_algebra_fkdet_properties {n : ℕ} (X Y K : Matrix (Fin n) (Fin n) ℂ) :
    strictMultiplicativity X Y ∧ matrixSpecialization X ∧ resonanceCriterion K := by
  refine ⟨?_, rfl, ?_⟩
  · unfold strictMultiplicativity fkDetRaw
    rw [Matrix.det_mul, norm_mul]
  · unfold resonanceCriterion fkDetRaw
    have hnorm : ‖Matrix.det (1 - K)‖ = 0 ↔ Matrix.det (1 - K) = 0 := by
      simp
    constructor
    · intro hzero hunit
      have hdet_zero : Matrix.det (1 - K) = 0 := hnorm.mp hzero
      have hdet_unit : IsUnit (Matrix.det (1 - K)) := (1 - K).isUnit_iff_isUnit_det.mp hunit
      exact hdet_unit.ne_zero hdet_zero
    · intro hnot
      apply hnorm.mpr
      by_contra hdet
      exact hnot ((1 - K).isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hdet))

end

end Omega.OperatorAlgebra
