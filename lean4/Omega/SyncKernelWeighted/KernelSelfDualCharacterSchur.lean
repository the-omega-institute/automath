import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open Matrix

noncomputable section

/-- The Schur-component similarity law coming from the tensor intertwiner. -/
def schurSimilarityLaw {n : Type*} [Fintype n] [DecidableEq n] (q : ℕ) (u chi_g₁ : ℂ)
    (Bχ Bχinv P : Matrix n n ℂ) : Prop :=
  P⁻¹ * Bχ * P = ((u * chi_g₁) ^ q) • Bχinv

/-- The determinant functional equation induced by the Schur-component similarity law. -/
def schurDeterminantFunctionalEquation {n : Type*} [Fintype n] [DecidableEq n] (q : ℕ) (u chi_g₁ z : ℂ)
    (Bχ Bχinv : Matrix n n ℂ) : Prop :=
  Matrix.det (1 - z • Bχ) = Matrix.det (1 - (((u * chi_g₁) ^ q) * z) • Bχinv)

/-- A concrete matrix-level version of the Schur-component functional equation:
the similarity relation on a Schur summand yields the determinant identity after conjugation. -/
theorem paper_kernel_self_dual_character_schur {n : Type*} [Fintype n] [DecidableEq n] (q : ℕ)
    (u chi_g₁ z : ℂ) (Bχ Bχinv P : Matrix n n ℂ) (hP : IsUnit P.det)
    (hsim : schurSimilarityLaw q u chi_g₁ Bχ Bχinv P) :
    schurSimilarityLaw q u chi_g₁ Bχ Bχinv P ∧
      schurDeterminantFunctionalEquation q u chi_g₁ z Bχ Bχinv := by
  refine ⟨hsim, ?_⟩
  have hP_unit : IsUnit P := P.isUnit_iff_isUnit_det.mpr hP
  rcases hP_unit with ⟨U, rfl⟩
  calc
    Matrix.det (1 - z • Bχ)
      = Matrix.det ((↑U : Matrix n n ℂ)⁻¹ * (1 - z • Bχ) * ↑U) := by
          symm
          exact Matrix.det_conj' U.isUnit (1 - z • Bχ)
    _ = Matrix.det (1 - z • (((u * chi_g₁) ^ q) • Bχinv)) := by
          congr 1
          rw [Matrix.mul_sub, Matrix.sub_mul]
          simp [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc, hsim]
    _ = Matrix.det (1 - ((((u * chi_g₁) ^ q) * z)) • Bχinv) := by
          congr 1
          ext i j
          simp [smul_smul, mul_left_comm, mul_comm]

end

end Omega.SyncKernelWeighted
