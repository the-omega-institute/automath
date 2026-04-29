import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.BoundaryAbsorptionJuliaCaratheodory

open Matrix
open scoped BigOperators ComplexOrder

namespace Omega.Zeta

theorem paper_xi_toeplitz_rank_stabilizes_to_distinct_unitcircle_roots (s N : ℕ)
    (ξ : Fin s → ℂ) (w : Fin s → ℝ) (hξ : Function.Injective ξ) (hw : ∀ k, 0 < w k) :
    Matrix.rank
        (fun i j : Fin (N + 1) =>
          ∑ k : Fin s, (w k : ℂ) * ξ k ^ (j : ℕ) * Complex.conj (ξ k ^ (i : ℕ))) =
      min (N + 1) s := by
  let T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
    fun i j => ∑ k : Fin s, (w k : ℂ) * ξ k ^ (j : ℕ) * Complex.conj (ξ k ^ (i : ℕ))
  let B : Matrix (Fin s) (Fin (N + 1)) ℂ :=
    fun k j => (Real.sqrt (w k) : ℂ) * ξ k ^ (j : ℕ)
  change T.rank = min (N + 1) s
  have hsqrt_ne_zero : ∀ k : Fin s, (Real.sqrt (w k) : ℂ) ≠ 0 := by
    intro k
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (hw k)))
  have hT : T = Bᴴ * B := by
    ext i j
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hsq : ((Real.sqrt (w k) : ℂ) ^ 2) = (w k : ℂ) := by
      exact_mod_cast (Real.sq_sqrt (le_of_lt (hw k)))
    rw [← hsq]
    simp [B, pow_two, mul_assoc, mul_left_comm, mul_comm]
  have hTB : T.rank = B.rank := by
    rw [hT, Matrix.rank_conjTranspose_mul_self]
  by_cases hs : s ≤ N + 1
  · let C : Matrix (Fin (N + 1)) (Fin s) ℂ := Bᴴ
    let M : Matrix (Fin s) (Fin s) ℂ := C.submatrix (Fin.castLE hs) (Equiv.refl (Fin s))
    have hsub : M.rank ≤ C.rank := by
      simpa [M, C] using
        (Matrix.rank_submatrix_le (f := Fin.castLE hs) (e := Equiv.refl (Fin s)) C)
    have hM :
        M =
          (Matrix.vandermonde ξ)ᴴ *
            Matrix.diagonal (fun k : Fin s => (Real.sqrt (w k) : ℂ)) := by
      ext i j
      rw [Matrix.mul_apply]
      simp [M, C, B, Matrix.vandermonde_apply, Matrix.diagonal_apply, mul_comm]
    have hdiag_unit :
        IsUnit (Matrix.diagonal (fun k : Fin s => (Real.sqrt (w k) : ℂ))).det := by
      apply isUnit_iff_ne_zero.mpr
      rw [Matrix.det_diagonal]
      exact Finset.prod_ne_zero_iff.mpr fun k _ => hsqrt_ne_zero k
    have hvand_unit : IsUnit (Matrix.vandermonde ξ).det := by
      exact isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hξ)
    have hM_rank : M.rank = s := by
      calc
        M.rank = ((Matrix.vandermonde ξ)ᴴ).rank := by
          rw [hM, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hdiag_unit]
        _ = (Matrix.vandermonde ξ).rank := by simp
        _ = s := by
          simpa using
            Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 hvand_unit)
    have hs_le_rank : s ≤ B.rank := by
      calc
        s = M.rank := hM_rank.symm
        _ ≤ C.rank := hsub
        _ = B.rank := by simp [C]
    have hB_le : B.rank ≤ s := by simpa using Matrix.rank_le_card_height B
    have hrank : B.rank = s := le_antisymm hB_le hs_le_rank
    rw [hTB, hrank, Nat.min_eq_right hs]
  · have hN : N + 1 ≤ s := Nat.le_of_lt (lt_of_not_ge hs)
    let z : Fin (N + 1) → ℂ := fun k => ξ (Fin.castLE hN k)
    let M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
      B.submatrix (Fin.castLE hN) (Equiv.refl (Fin (N + 1)))
    have hsub : M.rank ≤ B.rank := by
      simpa [M] using
        (Matrix.rank_submatrix_le (f := Fin.castLE hN) (e := Equiv.refl (Fin (N + 1))) B)
    have hz : Function.Injective z := by
      intro a b hab
      have hcast : Fin.castLE hN a = Fin.castLE hN b := hξ (by simpa [z] using hab)
      exact Fin.ext (by simpa using congrArg Fin.val hcast)
    have hM :
        M =
          Matrix.diagonal (fun k : Fin (N + 1) => (Real.sqrt (w (Fin.castLE hN k)) : ℂ)) *
            Matrix.vandermonde z := by
      ext i j
      rw [Matrix.mul_apply]
      simp [M, z, B, Matrix.vandermonde_apply, Matrix.diagonal_apply, mul_comm]
    have hdiag_unit :
        IsUnit
          (Matrix.diagonal
              (fun k : Fin (N + 1) => (Real.sqrt (w (Fin.castLE hN k)) : ℂ))).det := by
      apply isUnit_iff_ne_zero.mpr
      rw [Matrix.det_diagonal]
      exact Finset.prod_ne_zero_iff.mpr fun k _ => hsqrt_ne_zero (Fin.castLE hN k)
    have hvand_unit : IsUnit (Matrix.vandermonde z).det := by
      exact isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hz)
    have hM_rank : M.rank = N + 1 := by
      calc
        M.rank = (Matrix.vandermonde z).rank := by
          rw [hM, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdiag_unit]
        _ = N + 1 := by
          simpa using
            Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 hvand_unit)
    have hN_le_rank : N + 1 ≤ B.rank := by
      calc
        N + 1 = M.rank := hM_rank.symm
        _ ≤ B.rank := hsub
    have hB_le : B.rank ≤ N + 1 := by simpa using Matrix.rank_le_card_width B
    have hrank : B.rank = N + 1 := le_antisymm hB_le hN_le_rank
    rw [hTB, hrank, Nat.min_eq_left hN]

end Omega.Zeta
