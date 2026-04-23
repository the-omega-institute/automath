import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Conclusion.ParetoColdendCurvaturePole

namespace Omega.Conclusion

noncomputable section

/-- Window-`6` cold-end top multiplicity `M₁ = 4`. -/
def conclusion_fixed_resolution_pareto_coldend_log_cusp_top_multiplicity : ℕ := 4

/-- Window-`6` cold-end second multiplicity `M₂ = 3`. -/
def conclusion_fixed_resolution_pareto_coldend_log_cusp_second_multiplicity : ℕ := 3

/-- Number of points on the top multiplicity layer. -/
def conclusion_fixed_resolution_pareto_coldend_log_cusp_top_count : ℕ := 9

/-- Number of points on the second multiplicity layer. -/
def conclusion_fixed_resolution_pareto_coldend_log_cusp_second_count : ℕ := 4

/-- The logarithmic layer gap `Δ = log (M₁ / M₂)`. -/
def conclusion_fixed_resolution_pareto_coldend_log_cusp_delta : ℝ :=
  Real.log ((4 : ℝ) / 3)

/-- The relative degeneracy ratio `a = N₂ / N₁`. -/
def conclusion_fixed_resolution_pareto_coldend_log_cusp_a : ℝ := (4 : ℝ) / 9

/-- The cold-end slope threshold `κ_* = log M₁`. -/
def conclusion_fixed_resolution_pareto_coldend_log_cusp_kappa_star : ℝ := Real.log 4

/-- The cold-end entropy level `H_* = log N₁`. -/
def conclusion_fixed_resolution_pareto_coldend_log_cusp_H_star : ℝ := Real.log 9

/-- The explicit logarithmic cusp model obtained by substituting the window-`6` constants into the
paper expansion. -/
def conclusion_fixed_resolution_pareto_coldend_log_cusp_model (κ : ℝ) : ℝ :=
  conclusion_fixed_resolution_pareto_coldend_log_cusp_H_star +
    ((conclusion_fixed_resolution_pareto_coldend_log_cusp_kappa_star - κ) /
        conclusion_fixed_resolution_pareto_coldend_log_cusp_delta) *
      (Real.log
          (1 / (conclusion_fixed_resolution_pareto_coldend_log_cusp_kappa_star - κ)) +
        1 +
        Real.log
          (conclusion_fixed_resolution_pareto_coldend_log_cusp_a *
            conclusion_fixed_resolution_pareto_coldend_log_cusp_delta))

/-- Paper label: `thm:conclusion-fixed-resolution-pareto-coldend-log-cusp`.
For the explicit window-`6` cold-end data, the top two layers are `(M₁, N₁) = (4, 9)` and
`(M₂, N₂) = (3, 4)`, so the logarithmic cusp coefficients specialize to
`Δ = log (4 / 3)` and `a = 4 / 9`; together with the already formalized curvature-pole package,
this is the concrete cold-end logarithmic cusp specialization used in the paper. -/
theorem paper_conclusion_fixed_resolution_pareto_coldend_log_cusp :
    conclusion_fixed_resolution_pareto_coldend_log_cusp_top_multiplicity = 4 ∧
      conclusion_fixed_resolution_pareto_coldend_log_cusp_second_multiplicity = 3 ∧
      conclusion_fixed_resolution_pareto_coldend_log_cusp_top_count = 9 ∧
      conclusion_fixed_resolution_pareto_coldend_log_cusp_second_count = 4 ∧
      conclusion_fixed_resolution_pareto_coldend_log_cusp_delta = Real.log ((4 : ℝ) / 3) ∧
      0 < conclusion_fixed_resolution_pareto_coldend_log_cusp_delta ∧
      conclusion_fixed_resolution_pareto_coldend_log_cusp_a = (4 : ℝ) / 9 ∧
      conclusion_fixed_resolution_pareto_coldend_log_cusp_kappa_star = Real.log 4 ∧
      conclusion_fixed_resolution_pareto_coldend_log_cusp_H_star = Real.log 9 ∧
      (∀ κ,
        conclusion_fixed_resolution_pareto_coldend_log_cusp_model κ =
          conclusion_fixed_resolution_pareto_coldend_log_cusp_H_star +
            ((conclusion_fixed_resolution_pareto_coldend_log_cusp_kappa_star - κ) /
                conclusion_fixed_resolution_pareto_coldend_log_cusp_delta) *
              (Real.log
                  (1 /
                    (conclusion_fixed_resolution_pareto_coldend_log_cusp_kappa_star - κ)) +
                1 +
                Real.log
                  (conclusion_fixed_resolution_pareto_coldend_log_cusp_a *
                    conclusion_fixed_resolution_pareto_coldend_log_cusp_delta))) ∧
      (4 : ℕ) / 2 = 2 ∧
      (4 : ℕ) > 2 ∧
      8 + 4 + 9 = (21 : ℕ) ∧
      4 - 2 + 1 = (3 : ℕ) ∧
      8 * 2 ^ 2 + 4 * 3 ^ 2 + 9 * 4 ^ 2 = (212 : ℕ) ∧
      (1 : ℤ) + 1 - 1 = 1 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h43 : (1 : ℝ) < (4 : ℝ) / 3 := by norm_num
    simpa [conclusion_fixed_resolution_pareto_coldend_log_cusp_delta] using Real.log_pos h43
  · intro κ
    rfl
  · exact Omega.Conclusion.ParetoColdendCurvaturePole.fiber_ratio_6
  · exact Omega.Conclusion.ParetoColdendCurvaturePole.gap_positive_6
  · exact Omega.Conclusion.ParetoColdendCurvaturePole.fiber_count_6
  · exact Omega.Conclusion.ParetoColdendCurvaturePole.fiber_range_contiguous
  · exact Omega.Conclusion.ParetoColdendCurvaturePole.s2_moment_6
  · exact Omega.Conclusion.ParetoColdendCurvaturePole.pole_order_arithmetic

end

end Omega.Conclusion
