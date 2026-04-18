import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

open Matrix

namespace Omega.Zeta

/-- Concrete `Z/2`-double-cover package for the null spectral splitting. The lifted operator has
the symmetric block form `[[B₀,B₁],[B₁,B₀]]`, and the Hadamard change of basis separates the
even and odd sectors into the blocks `B₀ + B₁` and `B₀ - B₁`. -/
structure NullZ2SpectralSplittingData where
  n : ℕ
  B0 : Matrix (Fin n) (Fin n) ℂ
  B1 : Matrix (Fin n) (Fin n) ℂ

namespace NullZ2SpectralSplittingData

/-- The lifted block matrix on the two-sheeted cover. -/
def liftedMatrix (D : NullZ2SpectralSplittingData) :
    Matrix (Sum (Fin D.n) (Fin D.n)) (Sum (Fin D.n) (Fin D.n)) ℂ :=
  Matrix.fromBlocks D.B0 D.B1 D.B1 D.B0

/-- The `+1`-eigenspace block for the deck involution. -/
def baseMatrix (D : NullZ2SpectralSplittingData) : Matrix (Fin D.n) (Fin D.n) ℂ :=
  D.B0 + D.B1

/-- The `-1`-eigenspace block for the deck involution. -/
def betaMatrix (D : NullZ2SpectralSplittingData) : Matrix (Fin D.n) (Fin D.n) ℂ :=
  D.B0 - D.B1

/-- The unnormalized Hadamard-type basis change. -/
def hadamard (D : NullZ2SpectralSplittingData) :
    Matrix (Sum (Fin D.n) (Fin D.n)) (Sum (Fin D.n) (Fin D.n)) ℂ :=
  Matrix.fromBlocks (1 : Matrix (Fin D.n) (Fin D.n) ℂ) 1 1 (-1)

/-- The inverse of `hadamard`, scaled by `1/2`. -/
noncomputable def hadamardInv (D : NullZ2SpectralSplittingData) :
    Matrix (Sum (Fin D.n) (Fin D.n)) (Sum (Fin D.n) (Fin D.n)) ℂ :=
  (1 / 2 : ℂ) • D.hadamard

/-- The Hadamard change of basis diagonalizes the lifted matrix into the even and odd blocks. -/
def hasDirectSumSplitting (D : NullZ2SpectralSplittingData) : Prop :=
  D.hadamardInv * D.liftedMatrix * D.hadamard =
    Matrix.fromBlocks D.baseMatrix 0 0 D.betaMatrix

/-- The determinant of the lifted matrix factors through the even/odd block decomposition. -/
def determinantFactorization (D : NullZ2SpectralSplittingData) : Prop :=
  Matrix.det D.liftedMatrix = Matrix.det D.baseMatrix * Matrix.det D.betaMatrix

end NullZ2SpectralSplittingData

open NullZ2SpectralSplittingData

lemma hadamardInv_mul_hadamard (D : NullZ2SpectralSplittingData) :
    D.hadamardInv * D.hadamard = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [NullZ2SpectralSplittingData.hadamardInv, NullZ2SpectralSplittingData.hadamard,
      Matrix.fromBlocks_smul, Matrix.fromBlocks_multiply]
  all_goals
    by_cases h : i = j <;> simp [Matrix.one_apply, h] <;> norm_num

lemma hadamard_conjugates_lifted (D : NullZ2SpectralSplittingData) :
    D.hadamardInv * D.liftedMatrix * D.hadamard =
      Matrix.fromBlocks D.baseMatrix 0 0 D.betaMatrix := by
  ext i j <;> rcases i with i | i <;> rcases j with j | j <;>
    simp [NullZ2SpectralSplittingData.hadamardInv, NullZ2SpectralSplittingData.hadamard,
      NullZ2SpectralSplittingData.liftedMatrix, NullZ2SpectralSplittingData.baseMatrix,
      NullZ2SpectralSplittingData.betaMatrix, Matrix.fromBlocks_smul,
      Matrix.fromBlocks_multiply, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  all_goals
    ring

/-- The `Z/2`-symmetric lift splits into even and odd spectral sectors under the Hadamard
change of basis, so its determinant factors as the product of the two sector determinants.
    thm:xi-null-z2-spectral-splitting-doublecover -/
theorem paper_xi_null_z2_spectral_splitting_doublecover (D : NullZ2SpectralSplittingData) :
    D.hasDirectSumSplitting ∧ D.determinantFactorization := by
  refine ⟨hadamard_conjugates_lifted D, ?_⟩
  have hsplit := hadamard_conjugates_lifted D
  have hdet :
      Matrix.det D.hadamardInv * Matrix.det D.liftedMatrix * Matrix.det D.hadamard =
        Matrix.det D.baseMatrix * Matrix.det D.betaMatrix := by
    have := congrArg Matrix.det hsplit
    simpa [NullZ2SpectralSplittingData.hasDirectSumSplitting,
      NullZ2SpectralSplittingData.determinantFactorization, Matrix.det_mul,
      Matrix.det_fromBlocks_zero₂₁] using this
  have hchange :
      Matrix.det D.hadamardInv * Matrix.det D.hadamard = 1 := by
    have := congrArg Matrix.det (hadamardInv_mul_hadamard D)
    simpa [Matrix.det_mul] using this
  calc
    Matrix.det D.liftedMatrix
        = (Matrix.det D.hadamardInv * Matrix.det D.hadamard) * Matrix.det D.liftedMatrix := by
            simp [hchange]
    _ = Matrix.det D.hadamardInv * Matrix.det D.liftedMatrix * Matrix.det D.hadamard := by
          ring
    _ = Matrix.det D.baseMatrix * Matrix.det D.betaMatrix := hdet

end Omega.Zeta
