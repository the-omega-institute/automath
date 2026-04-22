import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-phase-residual-linearization-sqrt15`. The phase residual is
linearized at the slope `√15` by comparing against `√15 x`, using `||a| - |b|| ≤ |a - b|`,
the quadratic cosine defect bound, and the cubic Taylor remainder for sine on `|x| ≤ 1/10`. -/
theorem paper_pom_phase_residual_linearization_sqrt15 {x : Real} (hx : abs x <= 1 / 10) :
    abs (abs (1 - Real.cos x + Real.sqrt 15 * Real.sin x) - Real.sqrt 15 * abs x) <=
      2 * x ^ 2 := by
  have hx1 : abs x ≤ 1 := by
    linarith
  have hsqrt_nonneg : 0 ≤ Real.sqrt 15 := Real.sqrt_nonneg 15
  have hsqrt_le : Real.sqrt 15 ≤ 4 := by
    rw [Real.sqrt_le_iff]
    norm_num
  have hcos_abs : abs (1 - Real.cos x) ≤ x ^ 2 / 2 := by
    have hnonneg : 0 ≤ 1 - Real.cos x := sub_nonneg.mpr (Real.cos_le_one x)
    rw [abs_of_nonneg hnonneg]
    linarith [Real.one_sub_sq_div_two_le_cos (x := x)]
  have hsin_taylor := Real.sin_bound hx1
  have hsin_abs_aux :
      abs (Real.sin x - x) ≤ abs x ^ 4 * (5 / 96 : ℝ) + abs x ^ 3 / 6 := by
    calc
      abs (Real.sin x - x)
          = abs ((Real.sin x - (x - x ^ 3 / 6)) + ((x - x ^ 3 / 6) - x)) := by
              congr 1
              ring
      _ ≤ abs (Real.sin x - (x - x ^ 3 / 6)) + abs ((x - x ^ 3 / 6) - x) := by
            exact abs_add_le _ _
      _ ≤ abs x ^ 4 * (5 / 96 : ℝ) + abs (x ^ 3 / 6) := by
            have hsecond : abs ((x - x ^ 3 / 6) - x) = abs (x ^ 3 / 6) := by
              calc
                abs ((x - x ^ 3 / 6) - x) = abs (-(x ^ 3 / 6)) := by
                  congr 1
                  ring
                _ = abs (x ^ 3 / 6) := by rw [abs_neg]
            refine add_le_add hsin_taylor ?_
            exact hsecond.le
      _ = abs x ^ 4 * (5 / 96 : ℝ) + abs x ^ 3 / 6 := by
            rw [abs_div, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  have hsin_abs : abs (Real.sin x - x) ≤ x ^ 2 / 5 := by
    have hx_sq_small : abs x ^ 2 ≤ 1 / 100 := by
      calc
        abs x ^ 2 ≤ (1 / 10 : ℝ) ^ 2 := by
          gcongr
        _ = 1 / 100 := by norm_num
    have hfourth :
        abs x ^ 4 * (5 / 96 : ℝ) ≤ abs x ^ 2 / 1920 := by
      calc
        abs x ^ 4 * (5 / 96 : ℝ) = abs x ^ 2 * (abs x ^ 2 * (5 / 96 : ℝ)) := by
          ring
        _ ≤ abs x ^ 2 * ((1 / 100 : ℝ) * (5 / 96 : ℝ)) := by
          gcongr
        _ = abs x ^ 2 / 1920 := by
          ring
    have hcubic : abs x ^ 3 / 6 ≤ abs x ^ 2 / 60 := by
      calc
        abs x ^ 3 / 6 = abs x ^ 2 * (abs x / 6) := by
          ring
        _ ≤ abs x ^ 2 * ((1 / 10 : ℝ) / 6) := by
          gcongr
        _ = abs x ^ 2 / 60 := by
          ring
    have hpoly :
        abs x ^ 4 * (5 / 96 : ℝ) + abs x ^ 3 / 6 ≤ abs x ^ 2 / 5 := by
      calc
        abs x ^ 4 * (5 / 96 : ℝ) + abs x ^ 3 / 6
            ≤ abs x ^ 2 / 1920 + abs x ^ 2 / 60 := by
                exact add_le_add hfourth hcubic
        _ = (11 / 640 : ℝ) * abs x ^ 2 := by
              ring
        _ ≤ (1 / 5 : ℝ) * abs x ^ 2 := by
              have hcoeff : (11 / 640 : ℝ) ≤ 1 / 5 := by
                norm_num
              exact mul_le_mul_of_nonneg_right hcoeff (by positivity)
        _ = abs x ^ 2 / 5 := by ring
    have hx_sq : abs x ^ 2 = x ^ 2 := by
      simpa [pow_two] using (sq_abs x)
    calc
      abs (Real.sin x - x) ≤ abs x ^ 4 * (5 / 96 : ℝ) + abs x ^ 3 / 6 := hsin_abs_aux
      _ ≤ abs x ^ 2 / 5 := hpoly
      _ = x ^ 2 / 5 := by rw [hx_sq]
  have hstart :
      abs (abs (1 - Real.cos x + Real.sqrt 15 * Real.sin x) - Real.sqrt 15 * abs x) ≤
        abs ((1 - Real.cos x + Real.sqrt 15 * Real.sin x) - Real.sqrt 15 * x) := by
    simpa [abs_mul, abs_of_nonneg hsqrt_nonneg] using
      (abs_abs_sub_abs_le_abs_sub
        (1 - Real.cos x + Real.sqrt 15 * Real.sin x) (Real.sqrt 15 * x))
  calc
    abs (abs (1 - Real.cos x + Real.sqrt 15 * Real.sin x) - Real.sqrt 15 * abs x)
        ≤ abs ((1 - Real.cos x + Real.sqrt 15 * Real.sin x) - Real.sqrt 15 * x) := hstart
    _ = abs ((1 - Real.cos x) + Real.sqrt 15 * (Real.sin x - x)) := by ring_nf
    _ ≤ abs (1 - Real.cos x) + abs (Real.sqrt 15 * (Real.sin x - x)) := by
          exact abs_add_le (1 - Real.cos x) (Real.sqrt 15 * (Real.sin x - x))
    _ = abs (1 - Real.cos x) + Real.sqrt 15 * abs (Real.sin x - x) := by
          rw [abs_mul, abs_of_nonneg hsqrt_nonneg]
    _ ≤ x ^ 2 / 2 + Real.sqrt 15 * (x ^ 2 / 5) := by
          gcongr
    _ ≤ 2 * x ^ 2 := by
      have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
      calc
        x ^ 2 / 2 + Real.sqrt 15 * (x ^ 2 / 5)
            ≤ x ^ 2 / 2 + 4 * (x ^ 2 / 5) := by
                gcongr
        _ = (13 / 10 : ℝ) * x ^ 2 := by ring
        _ ≤ 2 * x ^ 2 := by
              have hcoeff : (13 / 10 : ℝ) ≤ 2 := by norm_num
              exact mul_le_mul_of_nonneg_right hcoeff hx2

end Omega.POM
