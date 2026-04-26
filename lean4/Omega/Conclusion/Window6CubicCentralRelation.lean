import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

open Matrix

theorem paper_conclusion_window6_cubic_central_relation (a b c : ℤ) :
    let M : Matrix (Fin 3) (Fin 3) ℤ := !![a, 0, 0; 0, b, 0; 0, 0, c]
    let Q : Matrix (Fin 3) (Fin 3) ℤ := !![0, 0, 1; 1, 0, 0; 0, 1, 0]
    (M * Q - Q * M) ^ 3 =
      ((a - b) * (a - c) * (b - c)) • (1 : Matrix (Fin 3) (Fin 3) ℤ) := by
  intro M Q
  have hcomm :
      M * Q - Q * M = !![0, 0, a - c; b - a, 0, 0; 0, c - b, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, Q]
  have hcube :
      (!![0, 0, a - c; b - a, 0, 0; 0, c - b, 0] :
          Matrix (Fin 3) (Fin 3) ℤ) ^ 3 =
        ((a - b) * (a - c) * (b - c)) • (1 : Matrix (Fin 3) (Fin 3) ℤ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three] <;>
      ring
  calc
    (M * Q - Q * M) ^ 3 =
        (!![0, 0, a - c; b - a, 0, 0; 0, c - b, 0] :
          Matrix (Fin 3) (Fin 3) ℤ) ^ 3 := by rw [hcomm]
    _ = ((a - b) * (a - c) * (b - c)) •
        (1 : Matrix (Fin 3) (Fin 3) ℤ) := hcube
