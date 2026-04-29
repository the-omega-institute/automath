import Mathlib

namespace Omega.POM

open Matrix

/-- The optimal coupling normal form: a positive diagonal refresh rate `κ` plus a rank-one term. -/
def diagonalRateOptimalCoupling (κ : ℝ) (u : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + Matrix.vecMulVec u u

/-- The unique `2 × 2` minor of the concrete optimal coupling. -/
def diagonalRateOptimalMinor (κ : ℝ) (u : Fin 2 → ℝ) : ℝ :=
  Matrix.det (diagonalRateOptimalCoupling κ u)

/-- Total positivity in the concrete `2 × 2` model is nonnegativity of its determinant. -/
def diagonalRateOptimalTP2 (κ : ℝ) (u : Fin 2 → ℝ) : Prop :=
  0 ≤ diagonalRateOptimalMinor κ u

/-- Strict positivity of the diagonal entries. -/
def diagonalRateOptimalDiagonalPositive (κ : ℝ) (u : Fin 2 → ℝ) : Prop :=
  ∀ i : Fin 2, 0 < diagonalRateOptimalCoupling κ u i i

/-- The rank-one part has vanishing `2 × 2` minor. -/
lemma diagonalRateOptimal_rankOne_minor_zero (u : Fin 2 → ℝ) :
    diagonalRateOptimalMinor 0 u = 0 := by
  simp [diagonalRateOptimalMinor, diagonalRateOptimalCoupling, Matrix.det_fin_two, Matrix.vecMulVec]
  ring_nf

/-- For the diagonal-plus-rank-one optimal coupling, the off-diagonal rank-one minor vanishes,
while the positive diagonal refresh rate makes the diagonal-containing minors strictly positive;
hence the concrete `2 × 2` optimal coupling is `TP₂`.
    thm:pom-diagonal-rate-optimal-tp2 -/
theorem paper_pom_diagonal_rate_optimal_tp2 (κ : ℝ) (u : Fin 2 → ℝ) (hk : 0 < κ) :
    diagonalRateOptimalMinor 0 u = 0 ∧
      diagonalRateOptimalTP2 κ u ∧
      diagonalRateOptimalDiagonalPositive κ u := by
  refine ⟨diagonalRateOptimal_rankOne_minor_zero u, ?_, ?_⟩
  · unfold diagonalRateOptimalTP2 diagonalRateOptimalMinor diagonalRateOptimalCoupling
    simp [Matrix.det_fin_two, Matrix.vecMulVec]
    nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
  · intro i
    fin_cases i <;>
      simp [diagonalRateOptimalCoupling, Matrix.vecMulVec] <;>
      nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), hk]

end Omega.POM
