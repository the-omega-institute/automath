import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Omega.Folding.MetallicCompressionLockingLambda2

namespace Omega.Folding

/-- The two-state transfer matrix for the metallic mean SFT. -/
def metallicTransferMatrix (A : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, A; 1, A - 1]

/-- The topological entropy package attached to the Perron root of the metallic transfer matrix. -/
noncomputable def metallicTopologicalEntropy (A : ℝ) : ℝ :=
  Real.log (metallicPerronRoot A)

lemma metallicTransferMatrix_charpoly (A : ℤ) :
    (metallicTransferMatrix A).charpoly =
      Polynomial.X ^ 2 - Polynomial.C A * Polynomial.X - 1 := by
  unfold metallicTransferMatrix Matrix.charpoly
  rw [Matrix.det_fin_two]
  simp only [Matrix.charmatrix_apply, Matrix.diagonal_apply, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Polynomial.C_1]
  simp (config := { decide := true }) only [if_true, if_false]
  rw [show Polynomial.C (A - 1) = Polynomial.C A - 1 by simp]
  ring_nf

lemma metallicPerronRoot_quadratic (A : ℝ) :
    metallicPerronRoot A ^ 2 - A * metallicPerronRoot A - 1 = 0 := by
  unfold metallicPerronRoot
  have hsqrt : Real.sqrt (A ^ 2 + 4) ^ 2 = A ^ 2 + 4 := by
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ A ^ 2 + 4)]
  nlinarith

lemma metallicPerronRoot_pos {A : ℝ} (hA : 1 ≤ A) : 0 < metallicPerronRoot A := by
  unfold metallicPerronRoot
  have hsqrt_nonneg : 0 ≤ Real.sqrt (A ^ 2 + 4) := Real.sqrt_nonneg _
  nlinarith

/-- Paper wrapper for the metallic-mean two-state SFT: the transfer matrix is
    `[[1, A], [1, A - 1]]`, its characteristic polynomial is `λ² - A λ - 1`, the Perron root is
    `(A + √(A² + 4)) / 2`, and the topological entropy is the logarithm of that Perron root.
    prop:metallic-two-state-sft -/
theorem paper_metallic_two_state_sft :
    (∀ A : ℤ,
      metallicTransferMatrix A = !![(1 : ℤ), A; 1, A - 1] ∧
      (metallicTransferMatrix A).charpoly =
        Polynomial.X ^ 2 - Polynomial.C A * Polynomial.X - 1) ∧
    (∀ A : ℝ, 1 ≤ A →
      let lam := metallicPerronRoot A
      lam = (A + Real.sqrt (A ^ 2 + 4)) / 2 ∧
      lam ^ 2 - A * lam - 1 = 0 ∧
      0 < lam ∧
      metallicTopologicalEntropy A = Real.log lam) := by
  refine ⟨?_, ?_⟩
  · intro A
    exact ⟨rfl, metallicTransferMatrix_charpoly A⟩
  · intro A hA
    refine ⟨rfl, metallicPerronRoot_quadratic A, metallicPerronRoot_pos hA, ?_⟩
    simp [metallicTopologicalEntropy]

end Omega.Folding
