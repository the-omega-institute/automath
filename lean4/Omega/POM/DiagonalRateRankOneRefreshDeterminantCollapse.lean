import Mathlib.Data.Matrix.Reflection
import Mathlib.Tactic

namespace Omega.POM

open Matrix

/-- Concrete `2 × 2` data for the diagonal-plus-rank-one determinant collapse. -/
structure DiagonalRateRankOneRefreshDeterminantCollapseData where
  a : ℚ
  b : ℚ
  p : ℚ
  q : ℚ

namespace DiagonalRateRankOneRefreshDeterminantCollapseData

/-- The diagonal refresh-defect rates `1 - r_x`. -/
def diagonalPart (D : DiagonalRateRankOneRefreshDeterminantCollapseData) :
    Matrix (Fin 2) (Fin 2) ℚ :=
  !![1 - D.a, 0;
    0, 1 - D.b]

/-- The rank-one refresh contribution `r πᵀ`. -/
def rankOnePart (D : DiagonalRateRankOneRefreshDeterminantCollapseData) :
    Matrix (Fin 2) (Fin 2) ℚ :=
  !![D.a * D.p, D.a * D.q;
    D.b * D.p, D.b * D.q]

/-- The full kernel `K = D + r πᵀ`. -/
def kernel (D : DiagonalRateRankOneRefreshDeterminantCollapseData) :
    Matrix (Fin 2) (Fin 2) ℚ :=
  D.diagonalPart + D.rankOnePart

/-- The scalar collapse term `πᵀ (I - z D)⁻¹ r`, written entrywise for the diagonal resolvent. -/
def scalarCollapse (D : DiagonalRateRankOneRefreshDeterminantCollapseData) (z : ℚ) : ℚ :=
  D.p * (1 - z * (1 - D.a))⁻¹ * D.a + D.q * (1 - z * (1 - D.b))⁻¹ * D.b

/-- Determinant factorization after separating the diagonal part from the rank-one refresh. -/
def detFactorization (D : DiagonalRateRankOneRefreshDeterminantCollapseData) : Prop :=
  ∀ z : ℚ,
    Matrix.det ((1 : Matrix (Fin 2) (Fin 2) ℚ) - z • D.kernel) =
      (1 - z * (1 - D.a)) * (1 - z * (1 - D.b)) -
        z * (D.p * D.a * (1 - z * (1 - D.b)) + D.q * D.b * (1 - z * (1 - D.a)))

/-- Expansion of the diagonal determinant as the product over the two diagonal entries. -/
def productExpansion (D : DiagonalRateRankOneRefreshDeterminantCollapseData) : Prop :=
  ∀ z : ℚ,
    Matrix.det ((1 : Matrix (Fin 2) (Fin 2) ℚ) - z • D.diagonalPart) =
      (1 - z * (1 - D.a)) * (1 - z * (1 - D.b))

/-- The scalar secular term expands entrywise because `(I - z D)⁻¹` is diagonal. -/
def scalarSecularEquation (D : DiagonalRateRankOneRefreshDeterminantCollapseData) : Prop :=
  ∀ z : ℚ,
    1 - z * (1 - D.a) ≠ 0 →
    1 - z * (1 - D.b) ≠ 0 →
    D.scalarCollapse z =
      D.p * D.a / (1 - z * (1 - D.a)) + D.q * D.b / (1 - z * (1 - D.b))

end DiagonalRateRankOneRefreshDeterminantCollapseData

open DiagonalRateRankOneRefreshDeterminantCollapseData

/-- The diagonal-rate rank-one refresh kernel has the determinant collapse predicted by the
matrix-determinant lemma, together with the explicit product formula for the diagonal factor and
the scalar secular equation obtained by expanding the diagonal resolvent. -/
theorem paper_pom_diagonal_rate_rank_one_refresh_determinant_collapse
    (D : DiagonalRateRankOneRefreshDeterminantCollapseData) :
    And D.detFactorization (And D.productExpansion D.scalarSecularEquation) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z
    simp [DiagonalRateRankOneRefreshDeterminantCollapseData.kernel,
      DiagonalRateRankOneRefreshDeterminantCollapseData.diagonalPart,
      DiagonalRateRankOneRefreshDeterminantCollapseData.rankOnePart, Matrix.det_fin_two]
    ring
  · intro z
    simp [DiagonalRateRankOneRefreshDeterminantCollapseData.diagonalPart, Matrix.det_fin_two]
  · intro z hza hzb
    unfold DiagonalRateRankOneRefreshDeterminantCollapseData.scalarCollapse
    simp [div_eq_mul_inv]
    ring

end Omega.POM
