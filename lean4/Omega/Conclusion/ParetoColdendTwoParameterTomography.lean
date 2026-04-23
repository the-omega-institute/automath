import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Conclusion.FixedResolutionParetoColdendLogCusp

namespace Omega.Conclusion

noncomputable section

/-- The coefficient read off from the leading `y log(1 / y)` term of the cold-end cusp. -/
def conclusion_pareto_coldend_two_parameter_tomography_first_limit : ℝ :=
  conclusion_fixed_resolution_pareto_coldend_log_cusp_delta⁻¹

/-- The constant term left after removing the leading logarithmic divergence. -/
def conclusion_pareto_coldend_two_parameter_tomography_second_limit : ℝ :=
  1 + Real.log
    (conclusion_fixed_resolution_pareto_coldend_log_cusp_a *
      conclusion_fixed_resolution_pareto_coldend_log_cusp_delta)

/-- Concrete tomography package extracted from the fixed-resolution cold-end cusp constants. -/
def conclusion_pareto_coldend_two_parameter_tomography_statement : Prop :=
  conclusion_pareto_coldend_two_parameter_tomography_first_limit =
      conclusion_fixed_resolution_pareto_coldend_log_cusp_delta⁻¹ ∧
    conclusion_pareto_coldend_two_parameter_tomography_second_limit =
      1 + Real.log
        (conclusion_fixed_resolution_pareto_coldend_log_cusp_a *
          conclusion_fixed_resolution_pareto_coldend_log_cusp_delta) ∧
    conclusion_fixed_resolution_pareto_coldend_log_cusp_delta =
      Real.log
        ((conclusion_fixed_resolution_pareto_coldend_log_cusp_top_multiplicity : ℝ) /
          conclusion_fixed_resolution_pareto_coldend_log_cusp_second_multiplicity) ∧
    conclusion_fixed_resolution_pareto_coldend_log_cusp_a =
      (conclusion_fixed_resolution_pareto_coldend_log_cusp_second_count : ℝ) /
        conclusion_fixed_resolution_pareto_coldend_log_cusp_top_count ∧
    0 < conclusion_fixed_resolution_pareto_coldend_log_cusp_delta ∧
    0 < conclusion_fixed_resolution_pareto_coldend_log_cusp_a ∧
    ∀ Δ a : ℝ,
      Δ = conclusion_pareto_coldend_two_parameter_tomography_first_limit⁻¹ →
      a = Real.exp (conclusion_pareto_coldend_two_parameter_tomography_second_limit - 1) / Δ →
      Δ = conclusion_fixed_resolution_pareto_coldend_log_cusp_delta ∧
        a = conclusion_fixed_resolution_pareto_coldend_log_cusp_a

/-- Paper label: `thm:conclusion-pareto-coldend-two-parameter-tomography`. -/
theorem paper_conclusion_pareto_coldend_two_parameter_tomography :
    conclusion_pareto_coldend_two_parameter_tomography_statement := by
  have hpackage := paper_conclusion_fixed_resolution_pareto_coldend_log_cusp
  have hdelta_eq :
      conclusion_fixed_resolution_pareto_coldend_log_cusp_delta = Real.log ((4 : ℝ) / 3) :=
    hpackage.2.2.2.2.1
  have hdelta_pos : 0 < conclusion_fixed_resolution_pareto_coldend_log_cusp_delta :=
    hpackage.2.2.2.2.2.1
  have ha_eq :
      conclusion_fixed_resolution_pareto_coldend_log_cusp_a = (4 : ℝ) / 9 :=
    hpackage.2.2.2.2.2.2.1
  have ha_pos : 0 < conclusion_fixed_resolution_pareto_coldend_log_cusp_a := by
    rw [ha_eq]
    norm_num
  have hdelta_ne : conclusion_fixed_resolution_pareto_coldend_log_cusp_delta ≠ 0 :=
    ne_of_gt hdelta_pos
  have haprod_pos :
      0 <
        conclusion_fixed_resolution_pareto_coldend_log_cusp_a *
          conclusion_fixed_resolution_pareto_coldend_log_cusp_delta :=
    mul_pos ha_pos hdelta_pos
  refine ⟨rfl, rfl, ?_, ?_, hdelta_pos, ha_pos, ?_⟩
  · simpa using hdelta_eq
  · rw [ha_eq]
    norm_num [conclusion_fixed_resolution_pareto_coldend_log_cusp_second_count,
      conclusion_fixed_resolution_pareto_coldend_log_cusp_top_count]
  · intro Δ a hΔ ha
    have hΔ' : Δ = conclusion_fixed_resolution_pareto_coldend_log_cusp_delta := by
      simpa [conclusion_pareto_coldend_two_parameter_tomography_first_limit, hdelta_ne] using hΔ
    constructor
    · exact hΔ'
    · calc
        a = Real.exp (conclusion_pareto_coldend_two_parameter_tomography_second_limit - 1) / Δ := ha
        _ =
            Real.exp
                (Real.log
                  (conclusion_fixed_resolution_pareto_coldend_log_cusp_a *
                    conclusion_fixed_resolution_pareto_coldend_log_cusp_delta)) /
              conclusion_fixed_resolution_pareto_coldend_log_cusp_delta := by
              rw [hΔ', conclusion_pareto_coldend_two_parameter_tomography_second_limit]
              ring_nf
        _ =
            (conclusion_fixed_resolution_pareto_coldend_log_cusp_a *
                conclusion_fixed_resolution_pareto_coldend_log_cusp_delta) /
              conclusion_fixed_resolution_pareto_coldend_log_cusp_delta := by
              rw [Real.exp_log haprod_pos]
        _ = conclusion_fixed_resolution_pareto_coldend_log_cusp_a := by
              field_simp [hdelta_ne]

end

end Omega.Conclusion
