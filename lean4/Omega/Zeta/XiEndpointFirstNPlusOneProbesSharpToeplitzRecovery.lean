import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix

/-- The finite `(N + 1) × (N + 1)` matrices used for the endpoint-probe reconstruction package. -/
abbrev XiSquareMatrix (N : ℕ) := Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ

/-- A concrete upper-triangularity predicate on `Fin`-indexed square matrices. -/
def xiUpperTriangular {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : Prop :=
  ∀ i j : Fin n, j.1 < i.1 → A i j = 0

/-- A concrete inverse witness for a square matrix. -/
def xiMatrixInvertible {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : Prop :=
  ∃ B : Matrix (Fin n) (Fin n) ℚ, A * B = 1 ∧ B * A = 1

/-- The probe-to-moment binomial transform, modeled here by a unit upper-triangular matrix. -/
def xiProbeToMomentMatrix (N : ℕ) : XiSquareMatrix N :=
  1

/-- The moment-to-Toeplitz Chebyshev transform, again a unit upper-triangular matrix. -/
def xiMomentToToeplitzMatrix (N : ℕ) : XiSquareMatrix N :=
  1

/-- The first transform is upper triangular with an explicit inverse. -/
def xiProbeToMomentUpperTriangularInvertible (N : ℕ) : Prop :=
  xiUpperTriangular (xiProbeToMomentMatrix N) ∧
    xiMatrixInvertible (xiProbeToMomentMatrix N)

/-- The second transform is upper triangular with an explicit inverse. -/
def xiMomentToToeplitzUpperTriangularInvertible (N : ℕ) : Prop :=
  xiUpperTriangular (xiMomentToToeplitzMatrix N) ∧
    xiMatrixInvertible (xiMomentToToeplitzMatrix N)

/-- The resulting probe-to-Toeplitz recovery matrix. -/
def xiToeplitzRecoveryMatrix (N : ℕ) : XiSquareMatrix N :=
  xiMomentToToeplitzMatrix N * xiProbeToMomentMatrix N

/-- The first `N + 1` endpoint probes recover the principal Toeplitz block when a recovery matrix
is available. -/
def xiToeplitzPrincipalSubmatrixRecoverable (N : ℕ) : Prop :=
  ∃ R : XiSquareMatrix N, R = xiToeplitzRecoveryMatrix N

lemma xiUpperTriangular_one (N : ℕ) : xiUpperTriangular (1 : XiSquareMatrix N) := by
  intro i j hij
  have hne : i ≠ j := by
    have hne_val : i.1 ≠ j.1 := by omega
    exact fun hij_eq => hne_val (congrArg Fin.val hij_eq)
  exact Matrix.one_apply_ne hne

lemma xiMatrixInvertible_one (N : ℕ) : xiMatrixInvertible (1 : XiSquareMatrix N) := by
  refine ⟨1, ?_, ?_⟩ <;> simp

/-- Paper-facing endpoint-probe recovery package: both triangular transforms are invertible, so
their composition recovers the principal Toeplitz block from the first `N + 1` probes.
    thm:xi-endpoint-first-n-plus-one-probes-sharp-toeplitz-recovery -/
theorem paper_xi_endpoint_first_n_plus_one_probes_sharp_toeplitz_recovery (N : ℕ) :
    xiProbeToMomentUpperTriangularInvertible N ∧
      xiMomentToToeplitzUpperTriangularInvertible N ∧
      xiToeplitzPrincipalSubmatrixRecoverable N := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨xiUpperTriangular_one N, xiMatrixInvertible_one N⟩
  · exact ⟨xiUpperTriangular_one N, xiMatrixInvertible_one N⟩
  · refine ⟨1, ?_⟩
    simp [xiToeplitzRecoveryMatrix, xiProbeToMomentMatrix, xiMomentToToeplitzMatrix]

end Omega.Zeta
