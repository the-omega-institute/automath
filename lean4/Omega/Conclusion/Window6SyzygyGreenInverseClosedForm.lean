import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.Conclusion

open Matrix

/-- Paper label: `thm:conclusion-window6-syzygy-green-inverse-closed-form`.
The relation `(AᵀA)^2 = 10 AᵀA` gives both the Green inverse identity and the Cartan
projector idempotence. -/
theorem paper_conclusion_window6_syzygy_green_inverse_closed_form
    (A : Matrix (Fin 3) (Fin 18) Rat) (AT : Matrix (Fin 18) (Fin 3) Rat)
    (K P : Matrix (Fin 18) (Fin 18) Rat)
    (hATA_sq : (AT * A) * (AT * A) = (10 : Rat) • (AT * A)) (hK : K = 1 + AT * A)
    (hP : P = (1 / 10 : Rat) • (AT * A)) :
    K * (1 - (1 / 11 : Rat) • (AT * A)) = 1 ∧ P * P = P := by
  let B : Matrix (Fin 18) (Fin 18) Rat := AT * A
  have hB : B * B = (10 : Rat) • B := by
    simpa [B] using hATA_sq
  constructor
  · subst K
    change (1 + B) * (1 - (1 / 11 : Rat) • B) = 1
    calc
      (1 + B) * (1 - (1 / 11 : Rat) • B) =
          (1 - (1 / 11 : Rat) • B) + (B - (1 / 11 : Rat) • (B * B)) := by
        rw [add_mul, one_mul, mul_sub, mul_one, mul_smul_comm]
      _ = 1 := by
        rw [hB]
        ext i j
        simp [Matrix.smul_apply]
        ring_nf
  · subst P
    change ((1 / 10 : Rat) • B) * ((1 / 10 : Rat) • B) = (1 / 10 : Rat) • B
    calc
      ((1 / 10 : Rat) • B) * ((1 / 10 : Rat) • B) =
          (1 / 10 : Rat) • ((1 / 10 : Rat) • (B * B)) := by
        rw [smul_mul_assoc, mul_smul_comm]
      _ = (1 / 10 : Rat) • B := by
        rw [hB]
        ext i j
        simp [Matrix.smul_apply]

end Omega.Conclusion
