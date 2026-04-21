import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

namespace Omega.Zeta

theorem paper_xi_time_part9xc_serrin_hankel_prony_rank_one (c : ℝ) (N : ℕ) :
    Matrix.rank (fun i j : Fin (N + 1) => Real.exp (((i.1 + j.1 : ℕ) : ℝ) * c)) = 1 := by
  let a : Fin (N + 1) → ℝ := fun i => Real.exp ((i.1 : ℝ) * c)
  let M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := Matrix.vecMulVec a a
  have hM :
      (fun i j : Fin (N + 1) => Real.exp (((i.1 + j.1 : ℕ) : ℝ) * c)) = M := by
    ext i j
    rw [show (((i.1 + j.1 : ℕ) : ℝ) * c) = (i.1 : ℝ) * c + (j.1 : ℝ) * c by
      norm_num [Nat.cast_add]
      ring, Real.exp_add]
    simp [M, a, Matrix.vecMulVec_apply]
  rw [hM]
  have hupper : M.rank ≤ 1 := Matrix.rank_vecMulVec_le a a
  have hcol : M.col 0 = a := by
    ext i
    simp [M, a, Matrix.vecMulVec_apply]
  have ha0 : a 0 = 1 := by
    simp [a]
  have ha_ne_zero : a ≠ 0 := by
    intro ha
    have hzero := congr_fun ha 0
    simp [ha0] at hzero
  have hrank_pos : 0 < M.rank := by
    rw [Matrix.rank]
    let x : LinearMap.range M.mulVecLin := ⟨a, ⟨Pi.single 0 (1 : ℝ), by
      simpa [Matrix.mulVec_single_one] using hcol⟩⟩
    have hx_ne : x ≠ 0 := by
      intro hx
      apply ha_ne_zero
      exact congrArg Subtype.val hx
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨x, hx_ne⟩
  have hlower : 1 ≤ M.rank := Nat.succ_le_of_lt hrank_pos
  exact le_antisymm hupper hlower

end Omega.Zeta
