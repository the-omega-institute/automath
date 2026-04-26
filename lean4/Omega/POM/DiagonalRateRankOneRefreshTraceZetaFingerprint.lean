import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Matrix.Reflection
import Mathlib.Tactic
import Omega.POM.DiagonalRateRankOneRefreshDeterminantCollapse

namespace Omega.POM

open Matrix

/-- Concrete trace/zeta package built on the verified rank-one determinant collapse. The finite
zeta function is recorded as the reciprocal characteristic polynomial, the poles are read from a
two-eigenvalue factorization, and the logarithmic zeta coefficients come from the finite spectral
expansion. -/
structure pom_diagonal_rate_rank_one_refresh_trace_zeta_fingerprint_data where
  collapseData : DiagonalRateRankOneRefreshDeterminantCollapseData
  z : ℚ
  charPoly : Polynomial ℚ
  zetaValue : ℚ
  eigenvalues : Fin 2 → ℚ
  logZetaTrace : ℕ → ℚ
  charPoly_matches_collapse :
    charPoly.eval z =
      (1 - z * (1 - collapseData.a)) * (1 - z * (1 - collapseData.b)) -
        z * (collapseData.p * collapseData.a * (1 - z * (1 - collapseData.b)) +
          collapseData.q * collapseData.b * (1 - z * (1 - collapseData.a)))
  spectral_factorization :
    charPoly.eval z = (1 - z * eigenvalues 0) * (1 - z * eigenvalues 1)
  zeta_is_reciprocal_charpoly :
    zetaValue = (charPoly.eval z)⁻¹
  logZetaTrace_is_spectral_sum :
    ∀ m : ℕ, logZetaTrace m = eigenvalues 0 ^ m + eigenvalues 1 ^ m

def pom_diagonal_rate_rank_one_refresh_trace_zeta_fingerprint_statement
    (D : pom_diagonal_rate_rank_one_refresh_trace_zeta_fingerprint_data) : Prop :=
  D.zetaValue =
      (Matrix.det ((1 : Matrix (Fin 2) (Fin 2) ℚ) - D.z • D.collapseData.kernel))⁻¹ ∧
    D.charPoly.eval D.z = (1 - D.z * D.eigenvalues 0) * (1 - D.z * D.eigenvalues 1) ∧
      ∀ m : ℕ, D.logZetaTrace m = D.eigenvalues 0 ^ m + D.eigenvalues 1 ^ m

/-- Paper label: `cor:pom-diagonal-rate-rank-one-refresh-trace-zeta-fingerprint`. The verified
determinant-collapse formula identifies the finite-dimensional zeta value with the reciprocal
characteristic polynomial, the eigenvalue factorization reads off the poles, and the trace package
records the logarithmic zeta series term-by-term. -/
theorem paper_pom_diagonal_rate_rank_one_refresh_trace_zeta_fingerprint
    (D : pom_diagonal_rate_rank_one_refresh_trace_zeta_fingerprint_data) :
    pom_diagonal_rate_rank_one_refresh_trace_zeta_fingerprint_statement D := by
  have hCollapse :=
    (paper_pom_diagonal_rate_rank_one_refresh_determinant_collapse D.collapseData).1 D.z
  have hDet :
      Matrix.det ((1 : Matrix (Fin 2) (Fin 2) ℚ) - D.z • D.collapseData.kernel) =
        D.charPoly.eval D.z := by
    calc
      Matrix.det ((1 : Matrix (Fin 2) (Fin 2) ℚ) - D.z • D.collapseData.kernel) =
          (1 - D.z * (1 - D.collapseData.a)) * (1 - D.z * (1 - D.collapseData.b)) -
            D.z *
              (D.collapseData.p * D.collapseData.a * (1 - D.z * (1 - D.collapseData.b)) +
                D.collapseData.q * D.collapseData.b * (1 - D.z * (1 - D.collapseData.a))) := by
            simpa using hCollapse
      _ = D.charPoly.eval D.z := by
        simpa using D.charPoly_matches_collapse.symm
  refine ⟨?_, D.spectral_factorization, D.logZetaTrace_is_spectral_sum⟩
  calc
    D.zetaValue = (D.charPoly.eval D.z)⁻¹ := D.zeta_is_reciprocal_charpoly
    _ = (Matrix.det ((1 : Matrix (Fin 2) (Fin 2) ℚ) - D.z • D.collapseData.kernel))⁻¹ := by
      rw [← hDet]

end Omega.POM
