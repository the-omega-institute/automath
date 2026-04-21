import Mathlib.Tactic
import Omega.POM.DiagonalRateAbsorbingFullVsDeletedInterlacing
import Omega.POM.DiagonalRateAbsorbingLaguerreInterlacing

namespace Omega.POM

/-- Secondary package for the full-vs-deleted interlacing certificate. The structure carries no
additional hypotheses; it simply exposes the paper-facing bundle assembled from the already
verified full-matrix and Laguerre witnesses. -/
structure DiagonalRateAbsorbingInterlacingData where

namespace DiagonalRateAbsorbingInterlacingData

/-- Combined interlacing package: the deleted block is the principal minor of the full matrix, the
full/deleted eigenvalues strictly interlace, and the deleted Laguerre secular equation has one
root in each complementary gap. -/
def fullVsDeletedInterlacing (_D : DiagonalRateAbsorbingInterlacingData) : Prop :=
  strictInterlacingChain ∧
    diagonalRateAbsorbingDeletedMatrix =
      Matrix.submatrix diagonalRateAbsorbingFullMatrix Fin.castSucc Fin.castSucc ∧
    (∀ z : ℝ,
      diagonalRateAbsorbingLaguerrePolynomial z = 0 ↔ z = 2 ∨ z = (20 : ℝ) / 3) ∧
    (∃! z : ℝ,
      diagonalRateAbsorbingLaguerreKappa < z ∧ z < 5 ∧
        diagonalRateAbsorbingLaguerrePolynomial z = 0) ∧
    ∃! z : ℝ,
      5 < z ∧ z < 8 ∧ diagonalRateAbsorbingLaguerrePolynomial z = 0

end DiagonalRateAbsorbingInterlacingData

/-- Paper label: `thm:pom-diagonal-rate-absorbing-full-vs-deleted-interlacing-secondary`. The
existing full-matrix interlacing certificate and the Laguerre secular-root certificate assemble
into the secondary full-vs-deleted interlacing package. -/
theorem paper_pom_diagonal_rate_absorbing_full_vs_deleted_interlacing_secondary
    (D : DiagonalRateAbsorbingInterlacingData) : D.fullVsDeletedInterlacing := by
  rcases paper_pom_diagonal_rate_absorbing_laguerre_interlacing with
    ⟨_, _, _, _, hRoots, hLeft, hRight⟩
  simpa [DiagonalRateAbsorbingInterlacingData.fullVsDeletedInterlacing] using
    show strictInterlacingChain ∧
        diagonalRateAbsorbingDeletedMatrix =
          Matrix.submatrix diagonalRateAbsorbingFullMatrix Fin.castSucc Fin.castSucc ∧
        (∀ z : ℝ,
          diagonalRateAbsorbingLaguerrePolynomial z = 0 ↔ z = 2 ∨ z = (20 : ℝ) / 3) ∧
        (∃! z : ℝ,
          diagonalRateAbsorbingLaguerreKappa < z ∧ z < 5 ∧
            diagonalRateAbsorbingLaguerrePolynomial z = 0) ∧
        ∃! z : ℝ,
          5 < z ∧ z < 8 ∧ diagonalRateAbsorbingLaguerrePolynomial z = 0 by
      exact ⟨paper_pom_diagonal_rate_absorbing_full_vs_deleted_interlacing,
        diagonalRateAbsorbing_deleted_is_principal_submatrix, hRoots, hLeft, hRight⟩

end Omega.POM
