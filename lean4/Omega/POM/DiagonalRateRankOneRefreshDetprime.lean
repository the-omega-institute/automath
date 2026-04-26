import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import Omega.POM.DiagonalRateRankOneRefreshDeterminantCollapse

namespace Omega.POM

open Matrix

/-- The deleted determinant remaining after factoring out the trivial `(1 - z)` term. -/
def pom_diagonal_rate_rank_one_refresh_detprime_deleted_det (a b p q : ℚ) : ℚ :=
  a * q + b * p

/-- Paper label: `cor:pom-diagonal-rate-rank-one-refresh-detprime`. For the `2 × 2` diagonal
rank-one refresh kernel with stationary weights `p + q = 1`, the determinant collapse from the
previous theorem factors off the trivial `(1 - z)` root, and the residual factor at `z = 1` is the
deleted determinant `aq + bp = ab (p / a + q / b)`. -/
theorem paper_pom_diagonal_rate_rank_one_refresh_detprime
    (a b p q : ℚ) (hprob : p + q = 1) (ha : a ≠ 0) (hb : b ≠ 0) :
    let D : DiagonalRateRankOneRefreshDeterminantCollapseData :=
      { a := a, b := b, p := p, q := q }
    (∀ z : ℚ,
        Matrix.det ((1 : Matrix (Fin 2) (Fin 2) ℚ) - z • D.kernel) =
          (1 - z) *
            (1 - z + z * pom_diagonal_rate_rank_one_refresh_detprime_deleted_det a b p q)) ∧
      pom_diagonal_rate_rank_one_refresh_detprime_deleted_det a b p q =
        a * b * (p / a + q / b) := by
  dsimp
  refine ⟨?_, ?_⟩
  · intro z
    have hcollapse :=
      (paper_pom_diagonal_rate_rank_one_refresh_determinant_collapse
        { a := a, b := b, p := p, q := q }).1 z
    calc
      Matrix.det
          ((1 : Matrix (Fin 2) (Fin 2) ℚ) -
            z • DiagonalRateRankOneRefreshDeterminantCollapseData.kernel
              { a := a, b := b, p := p, q := q }) =
        (1 - z * (1 - a)) * (1 - z * (1 - b)) -
          z * (p * a * (1 - z * (1 - b)) + q * b * (1 - z * (1 - a))) := hcollapse
      _ = (1 - z) *
            (1 - z + z * pom_diagonal_rate_rank_one_refresh_detprime_deleted_det a b p q) := by
        have hq : q = 1 - p := by
          linarith
        rw [pom_diagonal_rate_rank_one_refresh_detprime_deleted_det, hq]
        ring
  · rw [pom_diagonal_rate_rank_one_refresh_detprime_deleted_det]
    field_simp [ha, hb]
    ring

end Omega.POM
