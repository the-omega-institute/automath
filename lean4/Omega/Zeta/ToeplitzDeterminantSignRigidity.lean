import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

open Matrix

namespace Omega.Zeta

/-- Abstract determinant-sign package for a Toeplitz truncation that admits a congruence
decomposition into positive and negative definite blocks.
    cor:xi-toeplitz-determinant-sign-rigidity -/
theorem paper_xi_toeplitz_determinant_sign_rigidity
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (T R : Matrix (Sum m n) (Sum m n) ℝ)
    (P : Matrix m m ℝ) (G : Matrix n n ℝ)
    (hR : IsUnit R)
    (hcongr : Rᵀ * T * R = Matrix.fromBlocks P 0 0 (-G))
    (hP : P.PosDef) (hG : G.PosDef) :
    IsUnit T ∧
      Matrix.det T * Matrix.det R ^ 2 = (-1 : ℝ) ^ Fintype.card n * Matrix.det P * Matrix.det G ∧
      (0 < Matrix.det T ↔ Even (Fintype.card n)) ∧
      (Matrix.det T < 0 ↔ Odd (Fintype.card n)) := by
  have hdetP : 0 < Matrix.det P := hP.det_pos
  have hdetG : 0 < Matrix.det G := hG.det_pos
  have hprod_pos : 0 < Matrix.det P * Matrix.det G := mul_pos hdetP hdetG
  have hRdet_ne : Matrix.det R ≠ 0 := by
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det (A := R)).mp hR)
  have hRdet_sq_pos : 0 < Matrix.det R ^ 2 := sq_pos_iff.mpr hRdet_ne
  have hdet_eq :
      Matrix.det T * Matrix.det R ^ 2 =
        (-1 : ℝ) ^ Fintype.card n * Matrix.det P * Matrix.det G := by
    have h := congrArg Matrix.det hcongr
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_fromBlocks_zero₂₁,
      Matrix.det_neg] at h
    nlinarith
  have hTdet_ne : Matrix.det T ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hdet_eq
    have hpow_ne : ((-1 : ℝ) ^ Fintype.card n) ≠ 0 := by
      exact pow_ne_zero _ (by norm_num)
    have hrhs_ne : ((-1 : ℝ) ^ Fintype.card n) * Matrix.det P * Matrix.det G ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero hpow_ne (ne_of_gt hdetP)) (ne_of_gt hdetG)
    exact hrhs_ne hdet_eq.symm
  have hTunit : IsUnit T :=
    (Matrix.isUnit_iff_isUnit_det (A := T)).2 (isUnit_iff_ne_zero.mpr hTdet_ne)
  have hpos_even : 0 < Matrix.det T ↔ Even (Fintype.card n) := by
    constructor
    · intro hpos
      have hrhs_pos : 0 < ((-1 : ℝ) ^ Fintype.card n) * Matrix.det P * Matrix.det G := by
        simpa [hdet_eq] using mul_pos hpos hRdet_sq_pos
      by_cases hEven : Even (Fintype.card n)
      · exact hEven
      · have hOdd : Odd (Fintype.card n) := Nat.not_even_iff_odd.mp hEven
        rw [hOdd.neg_one_pow] at hrhs_pos
        have : Matrix.det P * Matrix.det G < 0 := by linarith
        linarith
    · intro hEven
      have hrhs_pos : 0 < ((-1 : ℝ) ^ Fintype.card n) * Matrix.det P * Matrix.det G := by
        rw [hEven.neg_one_pow]
        positivity
      have hmul_pos : 0 < Matrix.det T * Matrix.det R ^ 2 := by
        simpa [hdet_eq] using hrhs_pos
      exact (mul_pos_iff_of_pos_right hRdet_sq_pos).mp hmul_pos
  have hneg_odd : Matrix.det T < 0 ↔ Odd (Fintype.card n) := by
    constructor
    · intro hneg
      by_cases hOdd : Odd (Fintype.card n)
      · exact hOdd
      · have hEven : Even (Fintype.card n) := Nat.not_odd_iff_even.mp hOdd
        have hpos : 0 < Matrix.det T := hpos_even.2 hEven
        linarith
    · intro hOdd
      have hrhs_neg : ((-1 : ℝ) ^ Fintype.card n) * Matrix.det P * Matrix.det G < 0 := by
        rw [hOdd.neg_one_pow]
        have : Matrix.det P * Matrix.det G > 0 := hprod_pos
        linarith
      have hmul_neg : Matrix.det T * Matrix.det R ^ 2 < 0 := by
        simpa [hdet_eq] using hrhs_neg
      exact Left.neg_of_mul_neg_left hmul_neg (le_of_lt hRdet_sq_pos)
  exact ⟨hTunit, hdet_eq, hpos_even, hneg_odd⟩

end Omega.Zeta
