import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Zeta.XiTimePart70aUniformScaledDegeneracyQuantitative

namespace Omega.Zeta

noncomputable section

open xi_time_part70a_uniform_scaled_degeneracy_quantitative_data

/-- The two-terminal scaled moment constant obtained by applying the two-point limit to `y^q`. -/
def xi_time_part70a_scaled_moments_leading_constant_scaledMomentConstant (q : ℕ) : ℝ :=
  Real.goldenRatio⁻¹ + (Real.goldenRatio⁻¹ : ℝ) ^ (q + 2)

/-- The Binet-normalized leading constant for the unscaled bin-fold moment sum. -/
def xi_time_part70a_scaled_moments_leading_constant_binetLeadingConstant (q : ℕ) : ℝ :=
  (Real.goldenRatio + (Real.goldenRatio⁻¹ : ℝ) ^ q) / Real.sqrt 5

lemma xi_time_part70a_scaled_moments_leading_constant_weights_sum :
    Real.goldenRatio⁻¹ + (Real.goldenRatio⁻¹ : ℝ) ^ 2 = 1 := by
  have hφsq : (Real.goldenRatio : ℝ) ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
  have hφinv : (Real.goldenRatio⁻¹ : ℝ) = Real.goldenRatio - 1 := by
    have hφinv_conj : (Real.goldenRatio⁻¹ : ℝ) = -Real.goldenConj := by
      simpa [one_div] using Real.inv_goldenRatio
    nlinarith [hφinv_conj, Real.goldenRatio_add_goldenConj]
  rw [hφinv]
  nlinarith [hφsq]

/-- Exact zero-error two-state data for the monomial observable `y^q`. -/
def xi_time_part70a_scaled_moments_leading_constant_terminalData
    (q : ℕ) : xi_time_part70a_uniform_scaled_degeneracy_quantitative_data where
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_m := 0
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_terminalZeroWeight :=
    Real.goldenRatio⁻¹
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_terminalOneWeight :=
    (Real.goldenRatio⁻¹ : ℝ) ^ 2
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_valueZero := 1
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_valueOne := Real.goldenRatio⁻¹
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_observable := fun y : ℝ => y ^ q
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_lipschitzConstant := 0
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_errorConstant := 0
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_zeroWeight_nonneg := by
    positivity
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_oneWeight_nonneg := by
    positivity
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_weights_sum :=
    xi_time_part70a_scaled_moments_leading_constant_weights_sum
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_lipschitz_nonneg := by
    norm_num
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_error_nonneg := by
    norm_num
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_zero_approx := by
    simp
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_one_approx := by
    simp
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_lipschitz_zero := by
    simp
  xi_time_part70a_uniform_scaled_degeneracy_quantitative_lipschitz_one := by
    simp

lemma xi_time_part70a_scaled_moments_leading_constant_terminalAverage
    (q : ℕ) :
    xi_time_part70a_uniform_scaled_degeneracy_quantitative_terminalAverage
        (xi_time_part70a_scaled_moments_leading_constant_terminalData q) =
      xi_time_part70a_scaled_moments_leading_constant_scaledMomentConstant q := by
  simp [xi_time_part70a_uniform_scaled_degeneracy_quantitative_terminalAverage,
    xi_time_part70a_scaled_moments_leading_constant_terminalData,
    xi_time_part70a_scaled_moments_leading_constant_scaledMomentConstant, pow_add]
  ring

lemma xi_time_part70a_scaled_moments_leading_constant_binet_rewrite (q : ℕ) :
    Real.goldenRatio ^ 2 *
        xi_time_part70a_scaled_moments_leading_constant_scaledMomentConstant q =
      Real.goldenRatio + (Real.goldenRatio⁻¹ : ℝ) ^ q := by
  have hφne : (Real.goldenRatio : ℝ) ≠ 0 := Real.goldenRatio_ne_zero
  unfold xi_time_part70a_scaled_moments_leading_constant_scaledMomentConstant
  calc
    Real.goldenRatio ^ 2 *
        (Real.goldenRatio⁻¹ + (Real.goldenRatio⁻¹ : ℝ) ^ (q + 2)) =
        Real.goldenRatio +
          Real.goldenRatio ^ 2 * (Real.goldenRatio⁻¹ : ℝ) ^ (q + 2) := by
      field_simp [hφne]
    _ = Real.goldenRatio + (Real.goldenRatio⁻¹ : ℝ) ^ q := by
      congr 1
      rw [pow_add]
      calc
        Real.goldenRatio ^ 2 * ((Real.goldenRatio⁻¹ : ℝ) ^ q *
            (Real.goldenRatio⁻¹ : ℝ) ^ 2) =
            (Real.goldenRatio⁻¹ : ℝ) ^ q *
              (Real.goldenRatio ^ 2 * (Real.goldenRatio⁻¹ : ℝ) ^ 2) := by
          ring
        _ = (Real.goldenRatio⁻¹ : ℝ) ^ q := by
          have hunit : Real.goldenRatio ^ 2 * (Real.goldenRatio⁻¹ : ℝ) ^ 2 = 1 := by
            field_simp [hφne]
          rw [hunit, mul_one]

/-- Paper-facing scaled-moment package: the monomial observable gives the two-point moment
constant, and multiplying by the Fibonacci/Binet factor `φ^2 / sqrt 5` gives the advertised
leading coefficient. -/
def xi_time_part70a_scaled_moments_leading_constant_statement : Prop :=
  ∀ q : ℕ,
    xi_time_part70a_uniform_scaled_degeneracy_quantitative_terminalAverage
        (xi_time_part70a_scaled_moments_leading_constant_terminalData q) =
      xi_time_part70a_scaled_moments_leading_constant_scaledMomentConstant q ∧
    xi_time_part70a_uniform_scaled_degeneracy_quantitative_statement
      (xi_time_part70a_scaled_moments_leading_constant_terminalData q) ∧
    Real.goldenRatio ^ 2 *
        xi_time_part70a_scaled_moments_leading_constant_scaledMomentConstant q =
      Real.goldenRatio + (Real.goldenRatio⁻¹ : ℝ) ^ q ∧
    xi_time_part70a_scaled_moments_leading_constant_binetLeadingConstant q =
      (Real.goldenRatio ^ 2 *
          xi_time_part70a_scaled_moments_leading_constant_scaledMomentConstant q) /
        Real.sqrt 5

/-- Paper label: `cor:xi-time-part70a-scaled-moments-leading-constant`. -/
theorem paper_xi_time_part70a_scaled_moments_leading_constant :
    xi_time_part70a_scaled_moments_leading_constant_statement := by
  intro q
  have htwoPoint :=
    paper_xi_time_part70a_uniform_scaled_degeneracy_quantitative
      (xi_time_part70a_scaled_moments_leading_constant_terminalData q)
  have hrewrite := xi_time_part70a_scaled_moments_leading_constant_binet_rewrite q
  refine ⟨?_, htwoPoint, hrewrite, ?_⟩
  · exact xi_time_part70a_scaled_moments_leading_constant_terminalAverage q
  · unfold xi_time_part70a_scaled_moments_leading_constant_binetLeadingConstant
    rw [hrewrite]

end

end Omega.Zeta
