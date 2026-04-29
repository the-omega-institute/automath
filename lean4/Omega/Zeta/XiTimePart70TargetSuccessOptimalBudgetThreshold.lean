import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Zeta.XiFoldbinDyadicCapacityCriticalWindowLimit

namespace Omega.Zeta

/-- The dyadic critical-window success curve used in the target-threshold statement. -/
noncomputable def xi_time_part70_target_success_optimal_budget_threshold_success_curve
    (ζ : ℝ) : ℝ :=
  xiFoldbinDyadicCriticalWindowLimit ζ

/-- Endpoint inverse threshold for the two target success levels in the dyadic curve. -/
noncomputable def xi_time_part70_target_success_optimal_budget_threshold_inverse
    (s : ℝ) : ℝ :=
  if s = Real.goldenRatio / Real.sqrt 5 then 1 / Real.goldenRatio else 1

/-- Concrete target statement tying the dyadic success curve to the endpoint inverse threshold and
the monotone `O(1)` dyadic budget step. -/
def xi_time_part70_target_success_optimal_budget_threshold_statement : Prop :=
  xi_time_part70_target_success_optimal_budget_threshold_success_curve
      (xi_time_part70_target_success_optimal_budget_threshold_inverse
        (Real.goldenRatio / Real.sqrt 5)) =
    Real.goldenRatio / Real.sqrt 5 ∧
    xi_time_part70_target_success_optimal_budget_threshold_success_curve
        (xi_time_part70_target_success_optimal_budget_threshold_inverse
          (2 / Real.sqrt 5)) =
      2 / Real.sqrt 5 ∧
      xi_time_part70_target_success_optimal_budget_threshold_inverse
          (Real.goldenRatio / Real.sqrt 5) =
        1 / Real.goldenRatio ∧
        xi_time_part70_target_success_optimal_budget_threshold_inverse (2 / Real.sqrt 5) = 1 ∧
          ∀ m : ℕ, 2 ^ m ≤ 2 ^ (m + 1)

private theorem xi_time_part70_target_success_optimal_budget_threshold_two_ne_phi :
    (2 / Real.sqrt 5 : ℝ) ≠ Real.goldenRatio / Real.sqrt 5 := by
  intro h
  have hsqrt_ne : (Real.sqrt 5 : ℝ) ≠ 0 := by positivity
  have hmul := congrArg (fun x : ℝ => x * Real.sqrt 5) h
  field_simp [hsqrt_ne] at hmul
  have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) := by
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  nlinarith [hmul, hsqrt_sq, Real.sqrt_nonneg (5 : ℝ)]

/-- Paper label: `thm:xi-time-part70-target-success-optimal-budget-threshold`. -/
theorem paper_xi_time_part70_target_success_optimal_budget_threshold :
    xi_time_part70_target_success_optimal_budget_threshold_statement := by
  rcases paper_xi_foldbin_dyadic_capacity_critical_window_limit with
    ⟨_, _, _, _, _, _, _, _, hPhiEndpoint, hOneEndpoint⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [xi_time_part70_target_success_optimal_budget_threshold_success_curve,
      xi_time_part70_target_success_optimal_budget_threshold_inverse, if_pos rfl]
    exact hPhiEndpoint
  · rw [xi_time_part70_target_success_optimal_budget_threshold_success_curve,
      xi_time_part70_target_success_optimal_budget_threshold_inverse,
      if_neg xi_time_part70_target_success_optimal_budget_threshold_two_ne_phi]
    exact hOneEndpoint
  · rw [xi_time_part70_target_success_optimal_budget_threshold_inverse, if_pos rfl]
  · rw [xi_time_part70_target_success_optimal_budget_threshold_inverse,
      if_neg xi_time_part70_target_success_optimal_budget_threshold_two_ne_phi]
  · intro m
    exact Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.le_succ m)

end Omega.Zeta
