import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

open Real intervalIntegral

noncomputable section

/-- The split trigonometric integral obtained from the Cauchy--Poisson `L¹` profile after
`y = tan θ` and the sign change at `θ = π / 6`. -/
def xi_cauchy_poisson_tv_sharp_constant_integral : ℝ :=
  (2 / Real.pi) *
    ((∫ θ in (0 : ℝ)..Real.pi / 6,
        (1 - 4 * Real.sin θ ^ 2) * Real.cos θ ^ 2) +
      ∫ θ in Real.pi / 6..Real.pi / 2,
        (4 * Real.sin θ ^ 2 - 1) * Real.cos θ ^ 2)

private lemma xi_cauchy_poisson_tv_sharp_constant_left_integral :
    (∫ θ in (0 : ℝ)..Real.pi / 6,
        (1 - 4 * Real.sin θ ^ 2) * Real.cos θ ^ 2) =
      3 * Real.sqrt 3 / 16 := by
  have hrewrite :
      (fun θ : ℝ => (1 - 4 * Real.sin θ ^ 2) * Real.cos θ ^ 2) =
        fun θ : ℝ => Real.cos θ ^ 2 - 4 * (Real.sin θ ^ 2 * Real.cos θ ^ 2) := by
    funext θ
    ring
  have hsin_four_pi_six : Real.sin (4 * (Real.pi / 6)) = Real.sqrt 3 / 2 := by
    have hangle : 4 * (Real.pi / 6) = Real.pi - Real.pi / 3 := by ring
    rw [hangle, Real.sin_pi_sub, Real.sin_pi_div_three]
  rw [hrewrite]
  rw [intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_const_mul, integral_cos_sq, integral_sin_sq_mul_cos_sq]
    simp [Real.sin_zero, Real.cos_zero, Real.sin_pi_div_six, Real.cos_pi_div_six,
      hsin_four_pi_six]
    ring_nf
  · apply Continuous.intervalIntegrable
    fun_prop
  · apply Continuous.intervalIntegrable
    fun_prop

private lemma xi_cauchy_poisson_tv_sharp_constant_right_integral :
    (∫ θ in Real.pi / 6..Real.pi / 2,
        (4 * Real.sin θ ^ 2 - 1) * Real.cos θ ^ 2) =
      3 * Real.sqrt 3 / 16 := by
  have hrewrite :
      (fun θ : ℝ => (4 * Real.sin θ ^ 2 - 1) * Real.cos θ ^ 2) =
        fun θ : ℝ => 4 * (Real.sin θ ^ 2 * Real.cos θ ^ 2) - Real.cos θ ^ 2 := by
    funext θ
    ring
  have hsin_four_pi_six : Real.sin (4 * (Real.pi / 6)) = Real.sqrt 3 / 2 := by
    have hangle : 4 * (Real.pi / 6) = Real.pi - Real.pi / 3 := by ring
    rw [hangle, Real.sin_pi_sub, Real.sin_pi_div_three]
  have hsin_four_pi_two : Real.sin (4 * (Real.pi / 2)) = 0 := by
    have hangle : 4 * (Real.pi / 2) = 2 * Real.pi := by ring
    rw [hangle, Real.sin_two_pi]
  rw [hrewrite]
  rw [intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_const_mul, integral_cos_sq, integral_sin_sq_mul_cos_sq]
    simp [Real.sin_pi_div_six, Real.cos_pi_div_six, Real.sin_pi_div_two, Real.cos_pi_div_two,
      hsin_four_pi_six, hsin_four_pi_two]
    ring_nf
  · apply Continuous.intervalIntegrable
    fun_prop
  · apply Continuous.intervalIntegrable
    fun_prop

/-- Paper label: `thm:xi-cauchy-poisson-tv-sharp-constant`. -/
theorem paper_xi_cauchy_poisson_tv_sharp_constant :
    xi_cauchy_poisson_tv_sharp_constant_integral = 3 * Real.sqrt 3 / (4 * Real.pi) := by
  rw [xi_cauchy_poisson_tv_sharp_constant_integral,
    xi_cauchy_poisson_tv_sharp_constant_left_integral,
    xi_cauchy_poisson_tv_sharp_constant_right_integral]
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp [hpi]
  ring

end

end Omega.CircleDimension
