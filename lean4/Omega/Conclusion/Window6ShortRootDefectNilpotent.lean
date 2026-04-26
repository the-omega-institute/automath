import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-window6-short-root-defect-nilpotent`. The explicit
short-root commutator has one nonzero square entry and vanishing cube. -/
theorem paper_conclusion_window6_short_root_defect_nilpotent
    (Ns : Matrix (Fin 6) (Fin 6) Int)
    (hNs :
      Ns =
        (-2 : Int) • Matrix.single 3 2 (1 : Int) +
          (2 : Int) • Matrix.single 4 3 (1 : Int)) :
    Ns ^ 3 = 0 ∧ Ns ^ 2 ≠ 0 := by
  subst Ns
  simp only [Matrix.smul_single, smul_eq_mul, mul_one]
  let A : Matrix (Fin 6) (Fin 6) Int := Matrix.single 3 2 (-2 : Int)
  let B : Matrix (Fin 6) (Fin 6) Int := Matrix.single 4 3 (2 : Int)
  let N : Matrix (Fin 6) (Fin 6) Int :=
    A + B
  change N ^ 3 = 0 ∧ N ^ 2 ≠ 0
  have hAA : A * A = 0 := by
    simp [A]
  have hAB : A * B = 0 := by
    simp [A, B]
  have hBA : B * A = Matrix.single 4 2 (-4 : Int) := by
    simp [A, B]
  have hBB : B * B = 0 := by
    simp [B]
  have hsq :
      N ^ 2 = Matrix.single (4 : Fin 6) (2 : Fin 6) (-4 : Int) := by
    rw [pow_two]
    change (A + B) * (A + B) = Matrix.single (4 : Fin 6) (2 : Fin 6) (-4 : Int)
    rw [add_mul, mul_add, mul_add, hAA, hAB, hBA, hBB]
    simp
  have hCA : Matrix.single (4 : Fin 6) (2 : Fin 6) (-4 : Int) * A = 0 := by
    simp [A]
  have hCB : Matrix.single (4 : Fin 6) (2 : Fin 6) (-4 : Int) * B = 0 := by
    simp [B]
  have hcube : N ^ 3 = 0 := by
    rw [show (3 : Nat) = 2 + 1 by norm_num, pow_succ]
    rw [hsq]
    change Matrix.single (4 : Fin 6) (2 : Fin 6) (-4 : Int) * (A + B) = 0
    rw [mul_add, hCA, hCB]
    simp
  constructor
  · exact hcube
  · intro hzero
    have hsq_zero : Matrix.single (4 : Fin 6) (2 : Fin 6) (-4 : Int) = 0 := by
      simpa [hsq] using hzero
    have hentry' := congr_fun (congr_fun hsq_zero 4) 2
    norm_num [Matrix.single] at hentry'
