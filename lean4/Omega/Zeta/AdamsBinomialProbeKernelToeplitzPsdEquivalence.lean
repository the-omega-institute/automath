import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix

section

/-- The diagonal binomial/sign factor in the Adams probe basis. -/
def adamsBinomialProbeDiagonal (N : ℕ) : Fin (N + 1) → ℝ :=
  fun k => (Nat.choose N k : ℝ) * (-1 : ℝ) ^ (k : ℕ)

/-- The probe matrix with columns `b^(N)(ω_j)`. -/
def adamsBinomialProbeMatrix (N : ℕ) (ω : Fin (N + 1) → ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun k j => adamsBinomialProbeDiagonal N k * ω j ^ (k : ℕ)

/-- The scaled kernel Gram matrix attached to the Toeplitz block and probe phases. -/
noncomputable def adamsBinomialProbeKernelMatrix (N : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (ω : Fin (N + 1) → ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  (((4 : ℝ) ^ N)⁻¹) • ((adamsBinomialProbeMatrix N ω)ᴴ * T * adamsBinomialProbeMatrix N ω)

lemma adamsBinomialProbeMatrix_factorization (N : ℕ) (ω : Fin (N + 1) → ℝ) :
    adamsBinomialProbeMatrix N ω =
      Matrix.diagonal (adamsBinomialProbeDiagonal N) * (Matrix.vandermonde ω)ᵀ := by
  ext k j
  rw [Matrix.diagonal_mul]
  simp [adamsBinomialProbeMatrix, adamsBinomialProbeDiagonal, Matrix.vandermonde]

lemma adamsBinomialProbeDiagonal_ne_zero (N : ℕ) (k : Fin (N + 1)) :
    adamsBinomialProbeDiagonal N k ≠ 0 := by
  unfold adamsBinomialProbeDiagonal
  refine mul_ne_zero ?_ ?_
  · have hchoose : 0 < Nat.choose N (k : ℕ) := Nat.choose_pos (Fin.is_le k)
    exact_mod_cast hchoose.ne'
  · exact pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0)

lemma adamsBinomialProbeMatrix_det_ne_zero (N : ℕ) (ω : Fin (N + 1) → ℝ)
    (hω : Function.Injective ω) :
    (adamsBinomialProbeMatrix N ω).det ≠ 0 := by
  rw [adamsBinomialProbeMatrix_factorization, Matrix.det_mul, Matrix.det_transpose]
  refine mul_ne_zero ?_ ?_
  · rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun k hk => adamsBinomialProbeDiagonal_ne_zero N k
  · exact Matrix.det_vandermonde_ne_zero_iff.mpr hω

set_option maxHeartbeats 400000 in
/-- Paper-facing equivalence between Toeplitz positive semidefiniteness and positive
semidefiniteness of the Adams binomial probe Gram matrix. The first conjunct records the kernel as
the scaled congruence `4^{-N} Bᴴ T B`; the second uses the diagonal-times-Vandermonde
factorization of `B` to transfer PSD in both directions when the phases are distinct.
    thm:xi-adams-binomial-probe-kernel-toeplitz-psd-equivalence -/
theorem paper_xi_adams_binomial_probe_kernel_toeplitz_psd_equivalence
    (N : ℕ) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (ω : Fin (N + 1) → ℝ)
    (hω : Function.Injective ω) :
    adamsBinomialProbeKernelMatrix N T ω =
        (((4 : ℝ) ^ N)⁻¹) •
          ((adamsBinomialProbeMatrix N ω)ᴴ * T * adamsBinomialProbeMatrix N ω) ∧
      (T.PosSemidef ↔
        ((adamsBinomialProbeMatrix N ω)ᴴ * T * adamsBinomialProbeMatrix N ω).PosSemidef) := by
  have hBdetUnit : IsUnit (adamsBinomialProbeMatrix N ω).det :=
    isUnit_iff_ne_zero.mpr (adamsBinomialProbeMatrix_det_ne_zero N ω hω)
  have hBunit : IsUnit (adamsBinomialProbeMatrix N ω) := by
    refine ⟨(adamsBinomialProbeMatrix N ω).nonsingInvUnit hBdetUnit, rfl⟩
  constructor
  · rfl
  · simpa [star_eq_conjTranspose] using
      (IsUnit.posSemidef_star_left_conjugate_iff (U := adamsBinomialProbeMatrix N ω)
        (x := T) hBunit).symm

end

end Omega.Zeta
