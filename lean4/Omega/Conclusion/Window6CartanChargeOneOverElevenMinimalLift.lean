import Mathlib

namespace Omega.Conclusion

open Matrix

/-- Paper label: `thm:conclusion-window6-cartan-charge-one-over-eleven-minimal-lift`. -/
theorem paper_conclusion_window6_cartan_charge_one_over_eleven_minimal_lift
    (A : Matrix (Fin 3) (Fin 21) Real) (AT : Matrix (Fin 21) (Fin 3) Real)
    (hAA : A * AT = (11 : Real) • (1 : Matrix (Fin 3) (Fin 3) Real)) :
    A * ((1 / 11 : Real) • AT) = 1 ∧
      ((1 / 11 : Real) • AT) * A * ((1 / 11 : Real) • AT) =
        (1 / 11 : Real) • AT := by
  let B : Matrix (Fin 21) (Fin 3) Real := (1 / 11 : Real) • AT
  have hAB : A * B = 1 := by
    dsimp [B]
    calc
      A * ((1 / 11 : Real) • AT) = (1 / 11 : Real) • (A * AT) := by
        rw [Matrix.mul_smul]
      _ = (1 / 11 : Real) • ((11 : Real) • (1 : Matrix (Fin 3) (Fin 3) Real)) := by
        rw [hAA]
      _ = 1 := by
        ext i j
        by_cases hij : i = j
        · subst j
          simp
        · simp [hij]
  constructor
  · exact hAB
  · dsimp [B] at hAB ⊢
    calc
      ((1 / 11 : Real) • AT) * A * ((1 / 11 : Real) • AT) =
          ((1 / 11 : Real) • AT) * (A * ((1 / 11 : Real) • AT)) := by
        rw [Matrix.mul_assoc]
      _ = (1 / 11 : Real) • AT := by
        rw [hAB, Matrix.mul_one]

end Omega.Conclusion
