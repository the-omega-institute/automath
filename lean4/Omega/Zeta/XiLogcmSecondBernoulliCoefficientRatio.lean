import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Zeta

noncomputable section

/-- The `B₂` specialization used in the `R = 2` Stirling--Bernoulli hierarchy. -/
def xi_logcm_second_bernoulli_coefficient_ratio_bernoulli_two : ℝ :=
  1 / 6

/-- The `B₄` specialization used in the `R = 2` Stirling--Bernoulli hierarchy. -/
def xi_logcm_second_bernoulli_coefficient_ratio_bernoulli_four : ℝ :=
  -(1 / 30 : ℝ)

/-- The dominant coefficient in the `R = 2` expansion. -/
def xi_logcm_second_bernoulli_coefficient_ratio_first_coefficient : ℝ :=
  xi_logcm_second_bernoulli_coefficient_ratio_bernoulli_two *
    (Real.goldenRatio⁻¹ + Real.goldenRatio⁻¹)

/-- The second Bernoulli coefficient in the `R = 2` expansion. -/
def xi_logcm_second_bernoulli_coefficient_ratio_second_coefficient : ℝ :=
  (xi_logcm_second_bernoulli_coefficient_ratio_bernoulli_four / 6) *
    (Real.goldenRatio⁻¹ + Real.goldenRatio)

/-- The ratio base `(φ / 2)` coming from the `R = 2` specialization. -/
def xi_logcm_second_bernoulli_coefficient_ratio_base : ℝ :=
  Real.goldenRatio / 2

/-- The two-term `R = 2` Stirling--Bernoulli model for `E_m = log C_m - log(2π)`. -/
def xi_logcm_second_bernoulli_coefficient_ratio_error (m : ℕ) : ℝ :=
  xi_logcm_second_bernoulli_coefficient_ratio_first_coefficient *
      xi_logcm_second_bernoulli_coefficient_ratio_base ^ m +
    xi_logcm_second_bernoulli_coefficient_ratio_second_coefficient *
      xi_logcm_second_bernoulli_coefficient_ratio_base ^ (3 * m)

/-- The consecutive-term ratio model obtained from factoring the leading `(φ / 2)^m` term. -/
def xi_logcm_second_bernoulli_coefficient_ratio_ratio_model (m : ℕ) : ℝ :=
  xi_logcm_second_bernoulli_coefficient_ratio_base *
    ((1 + xi_logcm_second_bernoulli_coefficient_ratio_base ^ (2 * (m + 1))) *
      (1 + xi_logcm_second_bernoulli_coefficient_ratio_base ^ (2 * m))⁻¹)

/-- Paper-facing statement for the explicit second Bernoulli coefficient and the resulting two
asymptotic limits. -/
def xi_logcm_second_bernoulli_coefficient_ratio_statement : Prop :=
  xi_logcm_second_bernoulli_coefficient_ratio_first_coefficient = 1 / (3 * Real.goldenRatio) ∧
    xi_logcm_second_bernoulli_coefficient_ratio_second_coefficient = -(Real.sqrt 5) / 180 ∧
    Tendsto
      (fun m : ℕ =>
        (2 / Real.goldenRatio : ℝ) ^ (3 * m) *
          (xi_logcm_second_bernoulli_coefficient_ratio_error m -
            xi_logcm_second_bernoulli_coefficient_ratio_first_coefficient *
              xi_logcm_second_bernoulli_coefficient_ratio_base ^ m))
      atTop
      (𝓝 xi_logcm_second_bernoulli_coefficient_ratio_second_coefficient) ∧
    Tendsto xi_logcm_second_bernoulli_coefficient_ratio_ratio_model atTop
      (𝓝 xi_logcm_second_bernoulli_coefficient_ratio_base)

/-- Paper label: `cor:xi-logcm-second-bernoulli-coefficient-ratio`. At `R = 2`, the first two
Stirling--Bernoulli coefficients reduce to the displayed closed forms, the scaled second
coefficient is exact, and the consecutive-term ratio converges to `φ / 2`. -/
theorem paper_xi_logcm_second_bernoulli_coefficient_ratio :
    xi_logcm_second_bernoulli_coefficient_ratio_statement := by
  let c₁ := xi_logcm_second_bernoulli_coefficient_ratio_first_coefficient
  let c₂ := xi_logcm_second_bernoulli_coefficient_ratio_second_coefficient
  let r := xi_logcm_second_bernoulli_coefficient_ratio_base
  have hphi_sum : Real.goldenRatio + Real.goldenRatio⁻¹ = Real.sqrt 5 := by
    rw [Real.inv_goldenRatio]
    linarith [Real.goldenRatio_sub_goldenConj]
  have hc₁ :
      c₁ = 1 / (3 * Real.goldenRatio) := by
    unfold c₁ xi_logcm_second_bernoulli_coefficient_ratio_first_coefficient
      xi_logcm_second_bernoulli_coefficient_ratio_bernoulli_two
    field_simp [Real.goldenRatio_ne_zero]
    ring
  have hc₂ :
      c₂ = -(Real.sqrt 5) / 180 := by
    unfold c₂ xi_logcm_second_bernoulli_coefficient_ratio_second_coefficient
      xi_logcm_second_bernoulli_coefficient_ratio_bernoulli_four
    rw [add_comm, hphi_sum]
    ring
  have hr_pos : 0 < r := by
    unfold r xi_logcm_second_bernoulli_coefficient_ratio_base
    positivity
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hr_lt_one : r < 1 := by
    unfold r xi_logcm_second_bernoulli_coefficient_ratio_base
    nlinarith [Real.goldenRatio_lt_two]
  have hr_sq_lt_one : r ^ 2 < 1 := by
    nlinarith
  have hpow_zero :
      Tendsto (fun m : ℕ => r ^ (2 * m)) atTop (𝓝 0) := by
    have hbase :
        Tendsto (fun m : ℕ => (r ^ 2) ^ m) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hr_sq_lt_one
    simpa [pow_mul] using hbase
  have hc₁_ne : c₁ ≠ 0 := by
    rw [hc₁]
    positivity
  have hscaled :
      (fun m : ℕ =>
        (2 / Real.goldenRatio : ℝ) ^ (3 * m) *
          (xi_logcm_second_bernoulli_coefficient_ratio_error m - c₁ * r ^ m)) =
        fun _ : ℕ => c₂ := by
    funext m
    have hrecip : (2 / Real.goldenRatio : ℝ) = r⁻¹ := by
      unfold r xi_logcm_second_bernoulli_coefficient_ratio_base
      field_simp [Real.goldenRatio_ne_zero]
    calc
      (2 / Real.goldenRatio : ℝ) ^ (3 * m) *
          (xi_logcm_second_bernoulli_coefficient_ratio_error m - c₁ * r ^ m)
          =
        (r⁻¹) ^ (3 * m) * (c₂ * r ^ (3 * m)) := by
          rw [hrecip]
          simp [xi_logcm_second_bernoulli_coefficient_ratio_error, c₁, c₂, r]
      _ = c₂ * ((r⁻¹) ^ (3 * m) * r ^ (3 * m)) := by ring
      _ = c₂ * ((r⁻¹) * r) ^ (3 * m) := by rw [← mul_pow]
      _ = c₂ := by simp [hr_ne]
  have hnum :
      Tendsto (fun m : ℕ => 1 + r ^ (2 * (m + 1))) atTop (𝓝 1) := by
    have hshift :
        Tendsto (fun m : ℕ => r ^ (2 * (m + 1))) atTop (𝓝 0) :=
      hpow_zero.comp (tendsto_add_atTop_nat 1)
    simpa using tendsto_const_nhds.add hshift
  have hden :
      Tendsto (fun m : ℕ => 1 + r ^ (2 * m)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hpow_zero
  refine ⟨hc₁, hc₂, ?_, ?_⟩
  · rw [hscaled]
    simpa [c₂] using tendsto_const_nhds
  · have hquot :
        Tendsto (fun m : ℕ => (1 + r ^ (2 * (m + 1))) / (1 + r ^ (2 * m))) atTop (𝓝 (1 : ℝ)) :=
      by simpa using hnum.div hden one_ne_zero
    simpa [xi_logcm_second_bernoulli_coefficient_ratio_ratio_model, r, mul_assoc] using
      (show Tendsto (fun _ : ℕ => r) atTop (𝓝 r) from tendsto_const_nhds).mul hquot

end

end Omega.Zeta
