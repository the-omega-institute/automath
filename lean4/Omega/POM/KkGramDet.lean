import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

namespace Omega.POM

/-- The lower-triangular incidence matrix `B_k`. -/
def pom_kk_gram_det_incidence (k : ℕ) : Matrix (Fin k) (Fin k) ℤ :=
  fun i j => if j ≤ i then 1 else 0

/-- The Gram matrix `K_k = B_k B_kᵀ`, whose entries count common prefixes. -/
def pom_kk_gram_det_min_matrix (k : ℕ) : Matrix (Fin k) (Fin k) ℤ :=
  pom_kk_gram_det_incidence k * (pom_kk_gram_det_incidence k).transpose

/-- Paper-facing concrete determinant statement for `lem:pom-Kk-gram-det`. -/
def pom_kk_gram_det_statement (k : ℕ) : Prop :=
  Matrix.det (pom_kk_gram_det_min_matrix k) = 1

theorem pom_kk_gram_det_incidence_det (k : ℕ) :
    Matrix.det (pom_kk_gram_det_incidence k) = 1 := by
  classical
  have htri :
      (pom_kk_gram_det_incidence k).BlockTriangular (OrderDual.toDual : Fin k → _) := by
    intro i j hij
    simp only [pom_kk_gram_det_incidence]
    rw [if_neg]
    exact fun hji => (not_le_of_gt hij) hji
  rw [Matrix.det_of_lowerTriangular (pom_kk_gram_det_incidence k) htri]
  simp [pom_kk_gram_det_incidence]

/-- Paper label: `lem:pom-Kk-gram-det`. -/
theorem paper_pom_kk_gram_det (k : ℕ) : pom_kk_gram_det_statement k := by
  classical
  unfold pom_kk_gram_det_statement pom_kk_gram_det_min_matrix
  simp [Matrix.det_mul, Matrix.det_transpose, pom_kk_gram_det_incidence_det]

end Omega.POM
