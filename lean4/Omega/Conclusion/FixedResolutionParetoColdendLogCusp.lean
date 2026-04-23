import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Conclusion.ParetoColdendCurvaturePole
import Omega.Conclusion.RightEdgeVisiblePhasesSupportFunctionClosure

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

/-- The right-edge slope parameter `α_*` for the cold-end support plateau. -/
def conclusion_coldend_support_function_finite_integer_plateau_alpha_star : ℝ :=
  conclusion_fixed_resolution_pareto_coldend_log_cusp_kappa_star

/-- The normalized top branch has height `0`. -/
def conclusion_coldend_support_function_finite_integer_plateau_top_height : ℝ := 0

/-- The first secondary branch comes from the `d = 3` layer with multiplicity ratio `4 / 9`. -/
def conclusion_coldend_support_function_finite_integer_plateau_alpha2 : ℝ := Real.log 3

/-- Height of the `d = 3` secondary branch after subtracting the top height. -/
def conclusion_coldend_support_function_finite_integer_plateau_height2 : ℝ :=
  Real.log ((4 : ℝ) / 9)

/-- The second secondary branch comes from the `d = 2` layer with multiplicity ratio `8 / 9`. -/
def conclusion_coldend_support_function_finite_integer_plateau_alpha3 : ℝ := Real.log 2

/-- Height of the `d = 2` secondary branch after subtracting the top height. -/
def conclusion_coldend_support_function_finite_integer_plateau_height3 : ℝ :=
  Real.log ((8 : ℝ) / 9)

/-- The `d = 3` affine branch in the cold-end support function. -/
def conclusion_coldend_support_function_finite_integer_plateau_phase2 : ℝ × ℝ :=
  (conclusion_coldend_support_function_finite_integer_plateau_alpha2,
    conclusion_coldend_support_function_finite_integer_plateau_height2)

/-- The `d = 2` affine branch in the cold-end support function. -/
def conclusion_coldend_support_function_finite_integer_plateau_phase3 : ℝ × ℝ :=
  (conclusion_coldend_support_function_finite_integer_plateau_alpha3,
    conclusion_coldend_support_function_finite_integer_plateau_height3)

/-- The secondary branches below the normalized top branch. -/
def conclusion_coldend_support_function_finite_integer_plateau_secondary_phases :
    List (ℝ × ℝ) :=
  [conclusion_coldend_support_function_finite_integer_plateau_phase2,
    conclusion_coldend_support_function_finite_integer_plateau_phase3]

/-- The largest crossover scale between the top branch and the secondary affine branches. -/
def conclusion_coldend_support_function_finite_integer_plateau_a_plat : ℝ :=
  max
    (conclusion_coldend_support_function_finite_integer_plateau_height2 /
      (conclusion_coldend_support_function_finite_integer_plateau_alpha_star -
        conclusion_coldend_support_function_finite_integer_plateau_alpha2))
    (conclusion_coldend_support_function_finite_integer_plateau_height3 /
      (conclusion_coldend_support_function_finite_integer_plateau_alpha_star -
        conclusion_coldend_support_function_finite_integer_plateau_alpha3))

/-- Concrete finite-integer plateau statement for the cold-end support function. -/
def conclusion_coldend_support_function_finite_integer_plateau_statement : Prop :=
  ∀ a : ℤ,
    (a : ℝ) > conclusion_coldend_support_function_finite_integer_plateau_a_plat →
      Omega.Conclusion.conclusion_right_edge_visible_phases_support_function_closure_affine
          conclusion_coldend_support_function_finite_integer_plateau_alpha_star
          conclusion_coldend_support_function_finite_integer_plateau_phase2 (a : ℝ) <
        conclusion_coldend_support_function_finite_integer_plateau_top_height ∧
      Omega.Conclusion.conclusion_right_edge_visible_phases_support_function_closure_affine
          conclusion_coldend_support_function_finite_integer_plateau_alpha_star
          conclusion_coldend_support_function_finite_integer_plateau_phase3 (a : ℝ) <
        conclusion_coldend_support_function_finite_integer_plateau_top_height ∧
      Omega.Conclusion.conclusion_right_edge_visible_phases_support_function_closure_R
          conclusion_coldend_support_function_finite_integer_plateau_alpha_star
          conclusion_coldend_support_function_finite_integer_plateau_secondary_phases (a : ℝ) =
        conclusion_coldend_support_function_finite_integer_plateau_top_height ∧
      (a : ℝ) * conclusion_coldend_support_function_finite_integer_plateau_alpha_star +
          Omega.Conclusion.conclusion_right_edge_visible_phases_support_function_closure_R
            conclusion_coldend_support_function_finite_integer_plateau_alpha_star
            conclusion_coldend_support_function_finite_integer_plateau_secondary_phases (a : ℝ) =
        (a : ℝ) * conclusion_coldend_support_function_finite_integer_plateau_alpha_star +
          conclusion_coldend_support_function_finite_integer_plateau_top_height

/-- Paper label: `thm:conclusion-coldend-support-function-finite-integer-plateau`. -/
theorem paper_conclusion_coldend_support_function_finite_integer_plateau :
    conclusion_coldend_support_function_finite_integer_plateau_statement := by
  intro a ha
  have hden2 :
      0 <
        conclusion_coldend_support_function_finite_integer_plateau_alpha_star -
          conclusion_coldend_support_function_finite_integer_plateau_alpha2 := by
    unfold conclusion_coldend_support_function_finite_integer_plateau_alpha_star
      conclusion_fixed_resolution_pareto_coldend_log_cusp_kappa_star
      conclusion_coldend_support_function_finite_integer_plateau_alpha2
    have hlog : Real.log 3 < Real.log 4 := Real.log_lt_log (by positivity) (by norm_num)
    linarith
  have hden3 :
      0 <
        conclusion_coldend_support_function_finite_integer_plateau_alpha_star -
          conclusion_coldend_support_function_finite_integer_plateau_alpha3 := by
    unfold conclusion_coldend_support_function_finite_integer_plateau_alpha_star
      conclusion_fixed_resolution_pareto_coldend_log_cusp_kappa_star
      conclusion_coldend_support_function_finite_integer_plateau_alpha3
    have hlog : Real.log 2 < Real.log 4 := Real.log_lt_log (by positivity) (by norm_num)
    linarith
  have ha2 :
      conclusion_coldend_support_function_finite_integer_plateau_height2 /
          (conclusion_coldend_support_function_finite_integer_plateau_alpha_star -
            conclusion_coldend_support_function_finite_integer_plateau_alpha2) <
        (a : ℝ) := by
    exact lt_of_le_of_lt (le_max_left _ _) ha
  have ha3 :
      conclusion_coldend_support_function_finite_integer_plateau_height3 /
          (conclusion_coldend_support_function_finite_integer_plateau_alpha_star -
            conclusion_coldend_support_function_finite_integer_plateau_alpha3) <
        (a : ℝ) := by
    exact lt_of_le_of_lt (le_max_right _ _) ha
  have hmul2 :
      conclusion_coldend_support_function_finite_integer_plateau_height2 <
        (a : ℝ) *
          (conclusion_coldend_support_function_finite_integer_plateau_alpha_star -
            conclusion_coldend_support_function_finite_integer_plateau_alpha2) := by
    exact (_root_.div_lt_iff₀ hden2).mp ha2
  have hmul3 :
      conclusion_coldend_support_function_finite_integer_plateau_height3 <
        (a : ℝ) *
          (conclusion_coldend_support_function_finite_integer_plateau_alpha_star -
            conclusion_coldend_support_function_finite_integer_plateau_alpha3) := by
    exact (_root_.div_lt_iff₀ hden3).mp ha3
  have hbranch2 :
      Omega.Conclusion.conclusion_right_edge_visible_phases_support_function_closure_affine
          conclusion_coldend_support_function_finite_integer_plateau_alpha_star
          conclusion_coldend_support_function_finite_integer_plateau_phase2 (a : ℝ) <
        conclusion_coldend_support_function_finite_integer_plateau_top_height := by
    unfold Omega.Conclusion.conclusion_right_edge_visible_phases_support_function_closure_affine
      conclusion_coldend_support_function_finite_integer_plateau_phase2
      conclusion_coldend_support_function_finite_integer_plateau_top_height
    linarith
  have hbranch3 :
      Omega.Conclusion.conclusion_right_edge_visible_phases_support_function_closure_affine
          conclusion_coldend_support_function_finite_integer_plateau_alpha_star
          conclusion_coldend_support_function_finite_integer_plateau_phase3 (a : ℝ) <
        conclusion_coldend_support_function_finite_integer_plateau_top_height := by
    unfold Omega.Conclusion.conclusion_right_edge_visible_phases_support_function_closure_affine
      conclusion_coldend_support_function_finite_integer_plateau_phase3
      conclusion_coldend_support_function_finite_integer_plateau_top_height
    linarith
  have hR0 :
      Omega.Conclusion.conclusion_right_edge_visible_phases_support_function_closure_R
          conclusion_coldend_support_function_finite_integer_plateau_alpha_star
          conclusion_coldend_support_function_finite_integer_plateau_secondary_phases (a : ℝ) =
        0 := by
    have hbranch2_le :
        Omega.Conclusion.conclusion_right_edge_visible_phases_support_function_closure_affine
            conclusion_coldend_support_function_finite_integer_plateau_alpha_star
            conclusion_coldend_support_function_finite_integer_plateau_phase2 (a : ℝ) ≤
          0 := by
      simpa [conclusion_coldend_support_function_finite_integer_plateau_top_height] using hbranch2.le
    have hbranch3_le :
        Omega.Conclusion.conclusion_right_edge_visible_phases_support_function_closure_affine
            conclusion_coldend_support_function_finite_integer_plateau_alpha_star
            conclusion_coldend_support_function_finite_integer_plateau_phase3 (a : ℝ) ≤
          0 := by
      simpa [conclusion_coldend_support_function_finite_integer_plateau_top_height] using hbranch3.le
    unfold Omega.Conclusion.conclusion_right_edge_visible_phases_support_function_closure_R
      conclusion_coldend_support_function_finite_integer_plateau_secondary_phases
    change
      max
          (Omega.Conclusion.conclusion_right_edge_visible_phases_support_function_closure_affine
            conclusion_coldend_support_function_finite_integer_plateau_alpha_star
            conclusion_coldend_support_function_finite_integer_plateau_phase2 (a : ℝ))
          (max
            (Omega.Conclusion.conclusion_right_edge_visible_phases_support_function_closure_affine
              conclusion_coldend_support_function_finite_integer_plateau_alpha_star
              conclusion_coldend_support_function_finite_integer_plateau_phase3 (a : ℝ))
            0) =
        0
    rw [max_eq_right hbranch3_le, max_eq_right hbranch2_le]
  refine ⟨hbranch2, hbranch3, ?_, ?_⟩
  · simpa [conclusion_coldend_support_function_finite_integer_plateau_top_height] using hR0
  · simpa [conclusion_coldend_support_function_finite_integer_plateau_top_height] using congrArg
      (fun x =>
        (a : ℝ) * conclusion_coldend_support_function_finite_integer_plateau_alpha_star + x) hR0

end

end Omega.Conclusion
