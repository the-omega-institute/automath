import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Zeta

noncomputable section

/-- The terminal max-fiber exponential scale `(2 / φ)^m`. -/
def xi_time_part70d_maxfiber_excess_exact_main_term_lambda : ℝ :=
  2 / Real.goldenRatio

/-- The Binet coefficient for the average fiber size at the same exponential scale. -/
def xi_time_part70d_maxfiber_excess_exact_main_term_averageCoeff : ℝ :=
  Real.sqrt 5 / Real.goldenRatio ^ 2

/-- Concrete asymptotic data for the maximum fiber and the uniform average fiber. -/
structure xi_time_part70d_maxfiber_excess_exact_main_term_Data where
  xi_time_part70d_maxfiber_excess_exact_main_term_M : ℕ → ℝ
  xi_time_part70d_maxfiber_excess_exact_main_term_avg : ℕ → ℝ
  xi_time_part70d_maxfiber_excess_exact_main_term_M_asymptotic :
    Tendsto
      (fun m : ℕ =>
        xi_time_part70d_maxfiber_excess_exact_main_term_M m /
          xi_time_part70d_maxfiber_excess_exact_main_term_lambda ^ m) atTop (nhds 1)
  xi_time_part70d_maxfiber_excess_exact_main_term_avg_asymptotic :
    Tendsto
      (fun m : ℕ =>
        xi_time_part70d_maxfiber_excess_exact_main_term_avg m /
          xi_time_part70d_maxfiber_excess_exact_main_term_lambda ^ m) atTop
      (nhds xi_time_part70d_maxfiber_excess_exact_main_term_averageCoeff)

/-- The exact leading coefficient of the max-fiber excess after subtracting the Binet average. -/
def xi_time_part70d_maxfiber_excess_exact_main_term_Statement
    (D : xi_time_part70d_maxfiber_excess_exact_main_term_Data) : Prop :=
  Tendsto
    (fun m : ℕ =>
      (D.xi_time_part70d_maxfiber_excess_exact_main_term_M m -
          D.xi_time_part70d_maxfiber_excess_exact_main_term_avg m) /
        xi_time_part70d_maxfiber_excess_exact_main_term_lambda ^ m) atTop
    (nhds ((Real.goldenRatio ^ 4)⁻¹))

lemma xi_time_part70d_maxfiber_excess_exact_main_term_coeff :
    1 - xi_time_part70d_maxfiber_excess_exact_main_term_averageCoeff =
      (Real.goldenRatio ^ 4)⁻¹ := by
  unfold xi_time_part70d_maxfiber_excess_exact_main_term_averageCoeff
  rw [Real.goldenRatio]
  have hsqrt5_sq : (Real.sqrt 5 : ℝ) ^ 2 = 5 := by
    rw [Real.sq_sqrt]
    norm_num
  have hden : (1 + Real.sqrt 5 : ℝ) ≠ 0 := by positivity
  field_simp [hden]
  ring_nf
  nlinarith [hsqrt5_sq]

/-- Paper label: `cor:xi-time-part70d-maxfiber-excess-exact-main-term`. -/
theorem paper_xi_time_part70d_maxfiber_excess_exact_main_term
    (D : xi_time_part70d_maxfiber_excess_exact_main_term_Data) :
    xi_time_part70d_maxfiber_excess_exact_main_term_Statement D := by
  have hsub :=
    D.xi_time_part70d_maxfiber_excess_exact_main_term_M_asymptotic.sub
      D.xi_time_part70d_maxfiber_excess_exact_main_term_avg_asymptotic
  rw [xi_time_part70d_maxfiber_excess_exact_main_term_coeff] at hsub
  simpa [xi_time_part70d_maxfiber_excess_exact_main_term_Statement, div_eq_mul_inv,
    sub_eq_add_neg, add_mul] using hsub

end

end Omega.Zeta
