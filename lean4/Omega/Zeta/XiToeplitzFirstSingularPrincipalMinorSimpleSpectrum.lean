import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
import Omega.Zeta.XiToeplitzRankStabilizesDistinctUnitcircleRoots

open Matrix
open scoped BigOperators ComplexOrder

namespace Omega.Zeta

noncomputable section

/-- Concrete simple-spectrum Toeplitz data: `degree` distinct atoms with positive weights, observed
at the principal minor of order `principalOrder + 1`. -/
structure xi_toeplitz_first_singular_principal_minor_simple_spectrum_data where
  degree : ℕ
  principalOrder : ℕ
  root : Fin degree → ℂ
  weight : Fin degree → ℝ
  root_injective : Function.Injective root
  weight_pos : ∀ k, 0 < weight k

/-- The Toeplitz principal minor attached to the simple-spectrum atomic data. -/
def xi_toeplitz_first_singular_principal_minor_simple_spectrum_data.toeplitzMatrix
    (D : xi_toeplitz_first_singular_principal_minor_simple_spectrum_data) :
    Matrix (Fin (D.principalOrder + 1)) (Fin (D.principalOrder + 1)) ℂ :=
  fun i j =>
    ∑ k : Fin D.degree,
      (D.weight k : ℂ) * D.root k ^ (j : ℕ) * Complex.conj (D.root k ^ (i : ℕ))

/-- The principal minor has full rank below the degree threshold and drops rank exactly at and
beyond the degree, forcing singularity there. -/
def xi_toeplitz_first_singular_principal_minor_simple_spectrum_statement
    (D : xi_toeplitz_first_singular_principal_minor_simple_spectrum_data) : Prop :=
  let T := D.toeplitzMatrix
  Matrix.rank T = min (D.principalOrder + 1) D.degree ∧
    (D.principalOrder < D.degree → Matrix.rank T = D.principalOrder + 1) ∧
    (D.degree ≤ D.principalOrder → Matrix.rank T = D.degree ∧ T.det = 0)

/-- Paper label: `cor:xi-toeplitz-first-singular-principal-minor-simple-spectrum`. The Vandermonde
factorization from `paper_xi_toeplitz_rank_stabilizes_to_distinct_unitcircle_roots` gives the
exact rank formula; below the degree threshold the principal minor has full rank, while at and
beyond the degree threshold the rank drop forces singularity. -/
theorem paper_xi_toeplitz_first_singular_principal_minor_simple_spectrum
    (D : xi_toeplitz_first_singular_principal_minor_simple_spectrum_data) :
    xi_toeplitz_first_singular_principal_minor_simple_spectrum_statement D := by
  dsimp [xi_toeplitz_first_singular_principal_minor_simple_spectrum_statement]
  have hrank :
      Matrix.rank D.toeplitzMatrix = min (D.principalOrder + 1) D.degree := by
    simpa [xi_toeplitz_first_singular_principal_minor_simple_spectrum_data.toeplitzMatrix,
      Complex.conj_pow] using
      paper_xi_toeplitz_rank_stabilizes_to_distinct_unitcircle_roots D.degree D.principalOrder
        D.root D.weight D.root_injective D.weight_pos
  refine ⟨hrank, ?_, ?_⟩
  · intro hlt
    simpa [Nat.min_eq_left (Nat.succ_le_of_lt hlt)] using hrank
  · intro hge
    refine ⟨?_, ?_⟩
    · simpa [Nat.min_eq_right (le_trans hge (Nat.le_succ _))] using hrank
    · by_contra hdet
      have hunitDet : IsUnit D.toeplitzMatrix.det := isUnit_iff_ne_zero.mpr hdet
      have hunit : IsUnit D.toeplitzMatrix :=
        (Matrix.isUnit_iff_isUnit_det (A := D.toeplitzMatrix)).2 hunitDet
      have hfull : Matrix.rank D.toeplitzMatrix = D.principalOrder + 1 := by
        simpa using Matrix.rank_of_isUnit (A := D.toeplitzMatrix) hunit
      have hdrop : Matrix.rank D.toeplitzMatrix = D.degree := by
        simpa [Nat.min_eq_right (le_trans hge (Nat.le_succ _))] using hrank
      omega

end Omega.Zeta
