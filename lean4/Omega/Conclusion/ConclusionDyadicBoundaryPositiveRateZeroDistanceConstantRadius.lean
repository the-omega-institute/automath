import Mathlib.Tactic
import Omega.Conclusion.DyadicBoundaryCodeExactUniqueDecodingRadius

namespace Omega.Conclusion

open Filter
open scoped Topology

/-- The dyadic boundary code rate at fixed dimension. -/
noncomputable def conclusion_dyadic_boundary_positive_rate_zero_distance_constant_radius_rate
    (_m n : ℕ) : ℝ :=
  1 / n

/-- The closed-form relative distance of the dyadic boundary code. -/
noncomputable def conclusion_dyadic_boundary_positive_rate_zero_distance_constant_radius_relativeDistance
    (m n : ℕ) : ℝ :=
  2 / (((2 : ℝ) ^ m + 1) * (2 : ℝ) ^ (m * (n - 1)))

/-- Concrete statement package for the fixed-dimension dyadic boundary family:
positive rate, zero relative distance, and constant unique-decoding radius. -/
def paper_conclusion_dyadic_boundary_positive_rate_zero_distance_constant_radius_statement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    Tendsto
        (fun m : ℕ =>
          conclusion_dyadic_boundary_positive_rate_zero_distance_constant_radius_rate m n)
        atTop (𝓝 (1 / n : ℝ)) ∧
      Tendsto
        (fun m : ℕ =>
          conclusion_dyadic_boundary_positive_rate_zero_distance_constant_radius_relativeDistance
            m n)
        atTop (𝓝 0) ∧
        (∀ m : ℕ,
          dyadicBoundaryCodeUniqueDecodingRadius m n = n - 1)

lemma conclusion_dyadic_boundary_positive_rate_zero_distance_constant_radius_pow_tendsto :
    Tendsto (fun m : ℕ => (2 : ℝ) / ((2 : ℝ) ^ m + 1)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun m : ℕ => (2 : ℝ) ^ m) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hden : Tendsto (fun m : ℕ => (2 : ℝ) ^ m + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) hpow
  simpa [div_eq_mul_inv] using
    (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hden) :
      Tendsto (fun m : ℕ => (2 : ℝ) * (((2 : ℝ) ^ m + 1)⁻¹)) atTop (𝓝 (2 * 0)))

lemma conclusion_dyadic_boundary_positive_rate_zero_distance_constant_radius_relative_tendsto
    (n : ℕ) (_hn : 1 ≤ n) :
    Tendsto
      (fun m : ℕ =>
        conclusion_dyadic_boundary_positive_rate_zero_distance_constant_radius_relativeDistance
          m n)
      atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    conclusion_dyadic_boundary_positive_rate_zero_distance_constant_radius_pow_tendsto ?_ ?_
  · intro m
    unfold conclusion_dyadic_boundary_positive_rate_zero_distance_constant_radius_relativeDistance
    positivity
  · intro m
    unfold conclusion_dyadic_boundary_positive_rate_zero_distance_constant_radius_relativeDistance
    have hpow_ge_one : (1 : ℝ) ≤ (2 : ℝ) ^ (m * (n - 1)) := by
      exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    have hden_pos : 0 < (2 : ℝ) ^ m + 1 := by positivity
    have hle_den :
        (2 : ℝ) ^ m + 1 ≤ ((2 : ℝ) ^ m + 1) * (2 : ℝ) ^ (m * (n - 1)) := by
      nlinarith [mul_le_mul_of_nonneg_left hpow_ge_one hden_pos.le]
    exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hden_pos hle_den

/-- Paper label:
`cor:conclusion-dyadic-boundary-positive-rate-zero-distance-constant-radius`. -/
theorem paper_conclusion_dyadic_boundary_positive_rate_zero_distance_constant_radius :
    paper_conclusion_dyadic_boundary_positive_rate_zero_distance_constant_radius_statement := by
  intro n hn
  refine ⟨?_, ?_, ?_⟩
  · simp [conclusion_dyadic_boundary_positive_rate_zero_distance_constant_radius_rate]
  · exact
      conclusion_dyadic_boundary_positive_rate_zero_distance_constant_radius_relative_tendsto n hn
  · intro m
    exact
      (paper_conclusion_dyadic_boundary_code_exact_unique_decoding_radius m n hn).2.1

end Omega.Conclusion
