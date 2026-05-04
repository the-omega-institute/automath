import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete two-terminal-state data for the quantitative uniform scaled-degeneracy estimate. -/
structure xi_time_part70a_uniform_scaled_degeneracy_quantitative_data where
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_m : ℕ
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_terminalZeroWeight : ℝ
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_terminalOneWeight : ℝ
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_valueZero : ℝ
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_valueOne : ℝ
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_observable : ℝ → ℝ
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_lipschitzConstant : ℝ
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorConstant : ℝ
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_zeroWeight_nonneg :
    0 ≤ xi_time_part70a_uniform_scaled_degeneracy_quantitative_terminalZeroWeight
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_oneWeight_nonneg :
    0 ≤ xi_time_part70a_uniform_scaled_degeneracy_quantitative_terminalOneWeight
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_weights_sum :
    xi_time_part70a_uniform_scaled_degeneracy_quantitative_terminalZeroWeight +
      xi_time_part70a_uniform_scaled_degeneracy_quantitative_terminalOneWeight = 1
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_lipschitz_nonneg :
    0 ≤ xi_time_part70a_uniform_scaled_degeneracy_quantitative_lipschitzConstant
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_error_nonneg :
    0 ≤ xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorConstant
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_zero_approx :
    |xi_time_part70a_uniform_scaled_degeneracy_quantitative_valueZero - 1| ≤
      xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorConstant *
        (Real.goldenRatio / 2) ^
          xi_time_part70a_uniform_scaled_degeneracy_quantitative_m
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_one_approx :
    |xi_time_part70a_uniform_scaled_degeneracy_quantitative_valueOne -
        (Real.goldenRatio)⁻¹| ≤
      xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorConstant *
        (Real.goldenRatio / 2) ^
          xi_time_part70a_uniform_scaled_degeneracy_quantitative_m
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_lipschitz_zero :
    |xi_time_part70a_uniform_scaled_degeneracy_quantitative_observable
          xi_time_part70a_uniform_scaled_degeneracy_quantitative_valueZero -
        xi_time_part70a_uniform_scaled_degeneracy_quantitative_observable 1| ≤
      xi_time_part70a_uniform_scaled_degeneracy_quantitative_lipschitzConstant *
        |xi_time_part70a_uniform_scaled_degeneracy_quantitative_valueZero - 1|
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_lipschitz_one :
    |xi_time_part70a_uniform_scaled_degeneracy_quantitative_observable
          xi_time_part70a_uniform_scaled_degeneracy_quantitative_valueOne -
        xi_time_part70a_uniform_scaled_degeneracy_quantitative_observable
          (Real.goldenRatio)⁻¹| ≤
      xi_time_part70a_uniform_scaled_degeneracy_quantitative_lipschitzConstant *
        |xi_time_part70a_uniform_scaled_degeneracy_quantitative_valueOne -
          (Real.goldenRatio)⁻¹|

namespace xi_time_part70a_uniform_scaled_degeneracy_quantitative_data

/-- The geometric error scale in the two-state approximation. -/
def xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorScale
    (D : xi_time_part70a_uniform_scaled_degeneracy_quantitative_data) : ℝ :=
  (Real.goldenRatio / 2) ^
    D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_m

/-- The exact two-terminal average for the scaled degeneracy observable. -/
def xi_time_part70a_uniform_scaled_degeneracy_quantitative_terminalAverage
    (D : xi_time_part70a_uniform_scaled_degeneracy_quantitative_data) : ℝ :=
  D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_terminalZeroWeight *
      D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_observable
        D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_valueZero +
    D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_terminalOneWeight *
      D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_observable
        D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_valueOne

/-- The Fibonacci terminal-count model average. -/
def xi_time_part70a_uniform_scaled_degeneracy_quantitative_twoStateAverage
    (D : xi_time_part70a_uniform_scaled_degeneracy_quantitative_data) : ℝ :=
  D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_terminalZeroWeight *
      D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_observable 1 +
    D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_terminalOneWeight *
      D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_observable
        (Real.goldenRatio)⁻¹

/-- Paper-facing formulation: after splitting over the two terminal states, the expectation differs
from the Fibonacci two-state average by at most the Lipschitz constant times the uniform
two-state approximation error. -/
def xi_time_part70a_uniform_scaled_degeneracy_quantitative_statement
    (D : xi_time_part70a_uniform_scaled_degeneracy_quantitative_data) : Prop :=
  |D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_terminalAverage -
      D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_twoStateAverage| ≤
    D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_lipschitzConstant *
      D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorConstant *
        D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorScale

lemma xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorScale_nonneg
    (D : xi_time_part70a_uniform_scaled_degeneracy_quantitative_data) :
    0 ≤ D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorScale := by
  unfold xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorScale
  positivity

lemma xi_time_part70a_uniform_scaled_degeneracy_quantitative_zero_error
    (D : xi_time_part70a_uniform_scaled_degeneracy_quantitative_data) :
    |D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_observable
          D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_valueZero -
        D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_observable 1| ≤
      D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_lipschitzConstant *
        D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorConstant *
          D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorScale := by
  have hscale :
      0 ≤ D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorConstant *
        D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorScale := by
    exact mul_nonneg
      D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_error_nonneg
      (D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorScale_nonneg)
  calc
    |D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_observable
          D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_valueZero -
        D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_observable 1| ≤
        D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_lipschitzConstant *
          |D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_valueZero - 1| :=
      D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_lipschitz_zero
    _ ≤
        D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_lipschitzConstant *
          (D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorConstant *
            D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorScale) := by
      exact mul_le_mul_of_nonneg_left
        (by
          simpa [xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorScale] using
            D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_zero_approx)
        D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_lipschitz_nonneg
    _ =
        D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_lipschitzConstant *
          D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorConstant *
            D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorScale := by
      ring

lemma xi_time_part70a_uniform_scaled_degeneracy_quantitative_one_error
    (D : xi_time_part70a_uniform_scaled_degeneracy_quantitative_data) :
    |D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_observable
          D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_valueOne -
        D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_observable
          (Real.goldenRatio)⁻¹| ≤
      D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_lipschitzConstant *
        D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorConstant *
          D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorScale := by
  have hscale :
      0 ≤ D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorConstant *
        D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorScale := by
    exact mul_nonneg
      D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_error_nonneg
      (D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorScale_nonneg)
  calc
    |D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_observable
          D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_valueOne -
        D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_observable
          (Real.goldenRatio)⁻¹| ≤
        D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_lipschitzConstant *
          |D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_valueOne -
            (Real.goldenRatio)⁻¹| :=
      D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_lipschitz_one
    _ ≤
        D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_lipschitzConstant *
          (D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorConstant *
            D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorScale) := by
      exact mul_le_mul_of_nonneg_left
        (by
          simpa [xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorScale] using
            D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_one_approx)
        D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_lipschitz_nonneg
    _ =
        D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_lipschitzConstant *
          D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorConstant *
            D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorScale := by
      ring

end xi_time_part70a_uniform_scaled_degeneracy_quantitative_data

open xi_time_part70a_uniform_scaled_degeneracy_quantitative_data

/-- Paper label: `thm:xi-time-part70a-uniform-scaled-degeneracy-quantitative`. -/
theorem paper_xi_time_part70a_uniform_scaled_degeneracy_quantitative
    (D : xi_time_part70a_uniform_scaled_degeneracy_quantitative_data) :
    xi_time_part70a_uniform_scaled_degeneracy_quantitative_statement D := by
  let e0 :=
    D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_observable
        D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_valueZero -
      D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_observable 1
  let e1 :=
    D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_observable
        D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_valueOne -
      D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_observable
        (Real.goldenRatio)⁻¹
  let B :=
    D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_lipschitzConstant *
      D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorConstant *
        D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorScale
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg
      (mul_nonneg D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_lipschitz_nonneg
        D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_error_nonneg)
      (D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorScale_nonneg)
  have he0 : |e0| ≤ B := by
    dsimp [e0, B]
    exact D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_zero_error
  have he1 : |e1| ≤ B := by
    dsimp [e1, B]
    exact D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_one_error
  have hsplit :
      D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_terminalAverage -
          D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_twoStateAverage =
        D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_terminalZeroWeight * e0 +
          D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_terminalOneWeight * e1 := by
    dsimp [xi_time_part70a_uniform_scaled_degeneracy_quantitative_terminalAverage,
      xi_time_part70a_uniform_scaled_degeneracy_quantitative_twoStateAverage, e0, e1]
    ring
  rw [xi_time_part70a_uniform_scaled_degeneracy_quantitative_statement, hsplit]
  calc
    |D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_terminalZeroWeight * e0 +
        D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_terminalOneWeight * e1| ≤
        |D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_terminalZeroWeight * e0| +
          |D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_terminalOneWeight * e1| :=
      abs_add_le _ _
    _ =
        D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_terminalZeroWeight * |e0| +
          D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_terminalOneWeight * |e1| := by
      rw [abs_mul, abs_mul,
        abs_of_nonneg D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_zeroWeight_nonneg,
        abs_of_nonneg D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_oneWeight_nonneg]
    _ ≤
        D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_terminalZeroWeight * B +
          D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_terminalOneWeight * B := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left he0
          D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_zeroWeight_nonneg)
        (mul_le_mul_of_nonneg_left he1
          D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_oneWeight_nonneg)
    _ =
        (D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_terminalZeroWeight +
          D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_terminalOneWeight) * B := by
      ring
    _ = B := by
      rw [D.xi_time_part70a_uniform_scaled_degeneracy_quantitative_weights_sum]
      ring

end

end Omega.Zeta
