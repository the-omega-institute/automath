import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix

/-- The 4×4 Hankel matrix of weighted power sums s_k = Σ ωᵢ aᵢ^k.
    cor:xi-hankel-vs-prony-square-gap -/
def hankel4 (ω1 ω2 ω3 ω4 a1 a2 a3 a4 : ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  let s (k : ℕ) := ω1 * a1^k + ω2 * a2^k + ω3 * a3^k + ω4 * a4^k
  !![s 0, s 1, s 2, s 3;
     s 1, s 2, s 3, s 4;
     s 2, s 3, s 4, s 5;
     s 3, s 4, s 5, s 6]

set_option maxHeartbeats 16000000 in
/-- Expansion of 4×4 determinant into the standard 24-term formula. -/
private theorem det_fin_four {R : Type*} [CommRing R] (M : Matrix (Fin 4) (Fin 4) R) :
    M.det =
      M 0 0 * M 1 1 * M 2 2 * M 3 3 - M 0 0 * M 1 1 * M 2 3 * M 3 2
      - M 0 0 * M 1 2 * M 2 1 * M 3 3 + M 0 0 * M 1 2 * M 2 3 * M 3 1
      + M 0 0 * M 1 3 * M 2 1 * M 3 2 - M 0 0 * M 1 3 * M 2 2 * M 3 1
      - M 0 1 * M 1 0 * M 2 2 * M 3 3 + M 0 1 * M 1 0 * M 2 3 * M 3 2
      + M 0 1 * M 1 2 * M 2 0 * M 3 3 - M 0 1 * M 1 2 * M 2 3 * M 3 0
      - M 0 1 * M 1 3 * M 2 0 * M 3 2 + M 0 1 * M 1 3 * M 2 2 * M 3 0
      + M 0 2 * M 1 0 * M 2 1 * M 3 3 - M 0 2 * M 1 0 * M 2 3 * M 3 1
      - M 0 2 * M 1 1 * M 2 0 * M 3 3 + M 0 2 * M 1 1 * M 2 3 * M 3 0
      + M 0 2 * M 1 3 * M 2 0 * M 3 1 - M 0 2 * M 1 3 * M 2 1 * M 3 0
      - M 0 3 * M 1 0 * M 2 1 * M 3 2 + M 0 3 * M 1 0 * M 2 2 * M 3 1
      + M 0 3 * M 1 1 * M 2 0 * M 3 2 - M 0 3 * M 1 1 * M 2 2 * M 3 0
      - M 0 3 * M 1 2 * M 2 0 * M 3 1 + M 0 3 * M 1 2 * M 2 1 * M 3 0 := by
  rw [det_succ_row_zero, Fin.sum_univ_four]
  simp only [det_fin_three, submatrix_apply,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    show Fin.succ (2 : Fin 3) = (3 : Fin 4) from rfl,
    show (0 : Fin 4).succAbove (0 : Fin 3) = 1 from by decide,
    show (0 : Fin 4).succAbove (1 : Fin 3) = 2 from by decide,
    show (0 : Fin 4).succAbove (2 : Fin 3) = 3 from by decide,
    show (1 : Fin 4).succAbove (0 : Fin 3) = 0 from by decide,
    show (1 : Fin 4).succAbove (1 : Fin 3) = 2 from by decide,
    show (1 : Fin 4).succAbove (2 : Fin 3) = 3 from by decide,
    show (2 : Fin 4).succAbove (0 : Fin 3) = 0 from by decide,
    show (2 : Fin 4).succAbove (1 : Fin 3) = 1 from by decide,
    show (2 : Fin 4).succAbove (2 : Fin 3) = 3 from by decide,
    show (3 : Fin 4).succAbove (0 : Fin 3) = 0 from by decide,
    show (3 : Fin 4).succAbove (1 : Fin 3) = 1 from by decide,
    show (3 : Fin 4).succAbove (2 : Fin 3) = 2 from by decide,
    show (0 : Fin 4).val = 0 from rfl, show (1 : Fin 4).val = 1 from rfl,
    show (2 : Fin 4).val = 2 from rfl, show (3 : Fin 4).val = 3 from rfl]
  ring

-- Helper to extract entries from hankel4 via the defining function
private theorem hankel4_entry (ω1 ω2 ω3 ω4 a1 a2 a3 a4 : ℤ) (i j : Fin 4) :
    hankel4 ω1 ω2 ω3 ω4 a1 a2 a3 a4 i j =
      (ω1 * a1 ^ (i.val + j.val) + ω2 * a2 ^ (i.val + j.val) +
       ω3 * a3 ^ (i.val + j.val) + ω4 * a4 ^ (i.val + j.val)) := by
  fin_cases i <;> fin_cases j <;>
    simp [hankel4, of_apply, cons_val', pow_zero, mul_one, pow_succ]

set_option maxHeartbeats 16000000 in
/-- 4×4 Hankel determinant equals the product of weights times squared Vandermonde.
    cor:xi-hankel-vs-prony-square-gap -/
theorem hankel4_vandermonde_square
    (ω1 ω2 ω3 ω4 a1 a2 a3 a4 : ℤ) :
    (hankel4 ω1 ω2 ω3 ω4 a1 a2 a3 a4).det =
      ω1 * ω2 * ω3 * ω4 *
      (a2 - a1)^2 * (a3 - a1)^2 * (a4 - a1)^2 *
      (a3 - a2)^2 * (a4 - a2)^2 * (a4 - a3)^2 := by
  rw [det_fin_four]
  simp only [show ∀ i j : Fin 4,
    hankel4 ω1 ω2 ω3 ω4 a1 a2 a3 a4 i j =
      ω1 * a1 ^ (i.val + j.val) + ω2 * a2 ^ (i.val + j.val) +
      ω3 * a3 ^ (i.val + j.val) + ω4 * a4 ^ (i.val + j.val)
    from hankel4_entry ω1 ω2 ω3 ω4 a1 a2 a3 a4]
  simp only [show (0 : Fin 4).val = 0 from rfl, show (1 : Fin 4).val = 1 from rfl,
    show (2 : Fin 4).val = 2 from rfl, show (3 : Fin 4).val = 3 from rfl]
  ring

end Omega.Zeta
