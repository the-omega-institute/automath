import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.LeyangLissajousChebyshevResultant

namespace Omega.UnitCirclePhaseArithmetic

open Polynomial

/-- Integer-coefficient `X`-channel polynomial used in the cyclotomic elimination identity. -/
noncomputable def derived_lissajous_cyclotomic_resultant_poly_x (n : ℕ) : Polynomial ℤ :=
  Polynomial.Chebyshev.T ℤ n

/-- Integer-coefficient `Y`-channel polynomial used in the cyclotomic elimination identity. -/
noncomputable def derived_lissajous_cyclotomic_resultant_poly_y (n : ℕ) : Polynomial ℤ :=
  Polynomial.Chebyshev.T ℤ n

/-- For the cyclotomic phase `δ = 0`, the two integer-coefficient Chebyshev channels agree on the
Lissajous curve `x = cos (a t)`, `y = cos (b t)`. -/
abbrev derived_lissajous_cyclotomic_resultant_statement : Prop :=
  ∀ a b : ℕ, ∀ t : ℝ,
    let x := leyangLissajousX a t 0
    let y := leyangLissajousY b t
    Polynomial.eval₂ (Int.castRingHom ℝ) x
        (derived_lissajous_cyclotomic_resultant_poly_x b) =
      Polynomial.eval₂ (Int.castRingHom ℝ) y
        (derived_lissajous_cyclotomic_resultant_poly_y a)

/-- Paper label: `prop:derived-lissajous-cyclotomic-resultant`. -/
theorem paper_derived_lissajous_cyclotomic_resultant :
    derived_lissajous_cyclotomic_resultant_statement := by
  intro a b t
  dsimp [derived_lissajous_cyclotomic_resultant_statement]
  let x := leyangLissajousX a t 0
  let y := leyangLissajousY b t
  have hx :
      Polynomial.eval₂ (Int.castRingHom ℝ) x
          (derived_lissajous_cyclotomic_resultant_poly_x b) =
        Real.cos ((b : ℝ) * ((a : ℝ) * t)) := by
    rw [derived_lissajous_cyclotomic_resultant_poly_x]
    calc
      Polynomial.eval₂ (Int.castRingHom ℝ) x (Polynomial.Chebyshev.T ℤ b)
        = (Polynomial.Chebyshev.T ℝ b).eval x := by
            simpa [Polynomial.aeval_def] using
              (Polynomial.Chebyshev.aeval_T (R := ℤ) (R' := ℝ) x (b : ℤ))
      _ = Real.cos ((b : ℝ) * ((a : ℝ) * t)) := by
            simpa [x, leyangLissajousX] using
              (Polynomial.Chebyshev.T_real_cos ((a : ℝ) * t) (b : ℤ))
  have hy :
      Polynomial.eval₂ (Int.castRingHom ℝ) y
          (derived_lissajous_cyclotomic_resultant_poly_y a) =
        Real.cos ((a : ℝ) * ((b : ℝ) * t)) := by
    rw [derived_lissajous_cyclotomic_resultant_poly_y]
    calc
      Polynomial.eval₂ (Int.castRingHom ℝ) y (Polynomial.Chebyshev.T ℤ a)
        = (Polynomial.Chebyshev.T ℝ a).eval y := by
            simpa [Polynomial.aeval_def] using
              (Polynomial.Chebyshev.aeval_T (R := ℤ) (R' := ℝ) y (a : ℤ))
      _ = Real.cos ((a : ℝ) * ((b : ℝ) * t)) := by
            simpa [y, leyangLissajousY] using
              (Polynomial.Chebyshev.T_real_cos ((b : ℝ) * t) (a : ℤ))
  have hab : (b : ℝ) * ((a : ℝ) * t) = (a : ℝ) * ((b : ℝ) * t) := by ring
  calc
    Polynomial.eval₂ (Int.castRingHom ℝ) x
        (derived_lissajous_cyclotomic_resultant_poly_x b)
      = Real.cos ((b : ℝ) * ((a : ℝ) * t)) := hx
    _ = Real.cos ((a : ℝ) * ((b : ℝ) * t)) := by rw [hab]
    _ = Polynomial.eval₂ (Int.castRingHom ℝ) y
          (derived_lissajous_cyclotomic_resultant_poly_y a) := hy.symm

end Omega.UnitCirclePhaseArithmetic
