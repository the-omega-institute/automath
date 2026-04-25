import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

namespace Omega.POM

open Matrix

theorem paper_pom_bq_weighted_selfadjoint_binomial (q : ℕ) :
    let B : Matrix (Fin (q + 1)) (Fin (q + 1)) ℚ := fun i j => Nat.choose (q - j.1) i.1
    let W : Matrix (Fin (q + 1)) (Fin (q + 1)) ℚ :=
      fun i j => if i = j then (Nat.choose q i.1 : ℚ)⁻¹ else 0
    W * B = B.transpose * W := by
  let B : Matrix (Fin (q + 1)) (Fin (q + 1)) ℚ := fun i j => Nat.choose (q - j.1) i.1
  let d : Fin (q + 1) → ℚ := fun i => (Nat.choose q i.1 : ℚ)⁻¹
  have hW :
      (fun i j : Fin (q + 1) => if i = j then (Nat.choose q i.1 : ℚ)⁻¹ else 0) =
        Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [d]
    · simp [Matrix.diagonal, d, hij]
  simpa [B, hW] using
    (show Matrix.diagonal d * B = B.transpose * Matrix.diagonal d from by
      ext i j
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
      simp [B, d]
      by_cases hij : i.1 + j.1 ≤ q
      · have hi_le : i.1 ≤ q - j.1 := Nat.le_sub_of_add_le hij
        have hj_le : j.1 ≤ q - i.1 := Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hij)
        have hnat :
            Nat.choose (q - j.1) i.1 * Nat.choose q j.1 =
              Nat.choose q i.1 * Nat.choose (q - i.1) j.1 := by
          calc
            Nat.choose (q - j.1) i.1 * Nat.choose q j.1
                = Nat.choose q (q - j.1) * Nat.choose (q - j.1) i.1 := by
                    rw [Nat.choose_symm j.is_le, Nat.mul_comm]
            _ = Nat.choose q i.1 * Nat.choose (q - i.1) (q - j.1 - i.1) := by
                  simpa using Nat.choose_mul (n := q) (k := q - j.1) (s := i.1) hi_le
            _ = Nat.choose q i.1 * Nat.choose (q - i.1) j.1 := by
                  have hsub : q - j.1 - i.1 = q - i.1 - j.1 := by
                    omega
                  rw [hsub, Nat.choose_symm hj_le]
        have hqi : (Nat.choose q i.1 : ℚ) ≠ 0 := by
          exact_mod_cast Nat.choose_ne_zero i.is_le
        have hqj : (Nat.choose q j.1 : ℚ) ≠ 0 := by
          exact_mod_cast Nat.choose_ne_zero j.is_le
        have hnatQ :
            ((Nat.choose (q - j.1) i.1 : ℚ) * (Nat.choose q j.1 : ℚ)) =
              (Nat.choose q i.1 : ℚ) * (Nat.choose (q - i.1) j.1 : ℚ) := by
          exact_mod_cast hnat
        field_simp [hqi, hqj]
        simpa [mul_comm, mul_left_comm, mul_assoc] using hnatQ
      · have hleft : q - j.1 < i.1 := by
          omega
        have hright : q - i.1 < j.1 := by
          omega
        simp [Nat.choose_eq_zero_of_lt hleft, Nat.choose_eq_zero_of_lt hright])

end Omega.POM
