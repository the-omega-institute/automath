import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Conclusion.FoldbinQuantileThresholdRenyiInfinityUnification

namespace Omega.Zeta

noncomputable section

/-- Concrete data for the threshold-budget logarithmic jump.  The two constants are the
fold-bin quantile threshold and the `L^∞`/max-fiber exponent, both pinned to the existing
golden threshold constant; the two slope witnesses are pinned to the common logarithmic slope. -/
structure xi_foldbin_threshold_budget_logphi_jump_data where
  xi_foldbin_threshold_budget_logphi_jump_epsilon : ℝ
  xi_foldbin_threshold_budget_logphi_jump_thresholdConstant : ℝ
  xi_foldbin_threshold_budget_logphi_jump_maxFiberExponent : ℝ
  xi_foldbin_threshold_budget_logphi_jump_lowerSlope : ℝ
  xi_foldbin_threshold_budget_logphi_jump_upperSlope : ℝ
  xi_foldbin_threshold_budget_logphi_jump_epsilon_pos :
    0 < xi_foldbin_threshold_budget_logphi_jump_epsilon
  xi_foldbin_threshold_budget_logphi_jump_epsilon_subcritical :
    xi_foldbin_threshold_budget_logphi_jump_epsilon < Real.goldenRatio / Real.sqrt 5
  xi_foldbin_threshold_budget_logphi_jump_thresholdConstant_eq :
    xi_foldbin_threshold_budget_logphi_jump_thresholdConstant =
      Real.goldenRatio ^ (2 : ℕ) / Real.sqrt 5
  xi_foldbin_threshold_budget_logphi_jump_maxFiberExponent_eq :
    xi_foldbin_threshold_budget_logphi_jump_maxFiberExponent =
      Real.goldenRatio ^ (2 : ℕ) / Real.sqrt 5
  xi_foldbin_threshold_budget_logphi_jump_lowerSlope_eq :
    xi_foldbin_threshold_budget_logphi_jump_lowerSlope = Real.log Real.goldenRatio
  xi_foldbin_threshold_budget_logphi_jump_upperSlope_eq :
    xi_foldbin_threshold_budget_logphi_jump_upperSlope = Real.log Real.goldenRatio

namespace xi_foldbin_threshold_budget_logphi_jump_data

/-- Doubling the threshold budget gives a factor-two jump across the critical threshold. -/
def constantBudgetJump (D : xi_foldbin_threshold_budget_logphi_jump_data) : Prop :=
  (2 * D.xi_foldbin_threshold_budget_logphi_jump_thresholdConstant) /
      D.xi_foldbin_threshold_budget_logphi_jump_maxFiberExponent =
    2

/-- Both regimes keep the same exponential logarithmic slope. -/
def exponentialSlopeLocked (D : xi_foldbin_threshold_budget_logphi_jump_data) : Prop :=
  D.xi_foldbin_threshold_budget_logphi_jump_lowerSlope = Real.log Real.goldenRatio ∧
    D.xi_foldbin_threshold_budget_logphi_jump_upperSlope = Real.log Real.goldenRatio ∧
      D.xi_foldbin_threshold_budget_logphi_jump_lowerSlope =
        D.xi_foldbin_threshold_budget_logphi_jump_upperSlope

end xi_foldbin_threshold_budget_logphi_jump_data

/-- Paper label: `thm:xi-foldbin-threshold-budget-logphi-jump`. -/
theorem paper_xi_foldbin_threshold_budget_logphi_jump
    (D : xi_foldbin_threshold_budget_logphi_jump_data) :
    D.constantBudgetJump ∧ D.exponentialSlopeLocked := by
  have hcommon :
      D.xi_foldbin_threshold_budget_logphi_jump_thresholdConstant =
        D.xi_foldbin_threshold_budget_logphi_jump_maxFiberExponent :=
    Omega.Conclusion.paper_conclusion_foldbin_quantile_threshold_renyi_infty_unification
      D.xi_foldbin_threshold_budget_logphi_jump_epsilon
      D.xi_foldbin_threshold_budget_logphi_jump_thresholdConstant
      D.xi_foldbin_threshold_budget_logphi_jump_maxFiberExponent
      D.xi_foldbin_threshold_budget_logphi_jump_epsilon_pos
      D.xi_foldbin_threshold_budget_logphi_jump_epsilon_subcritical
      D.xi_foldbin_threshold_budget_logphi_jump_thresholdConstant_eq
      D.xi_foldbin_threshold_budget_logphi_jump_maxFiberExponent_eq
  have hmax_ne :
      D.xi_foldbin_threshold_budget_logphi_jump_maxFiberExponent ≠ 0 := by
    rw [D.xi_foldbin_threshold_budget_logphi_jump_maxFiberExponent_eq]
    positivity
  refine ⟨?_, ?_, ?_⟩
  · calc
      (2 * D.xi_foldbin_threshold_budget_logphi_jump_thresholdConstant) /
          D.xi_foldbin_threshold_budget_logphi_jump_maxFiberExponent =
          (2 * D.xi_foldbin_threshold_budget_logphi_jump_maxFiberExponent) /
            D.xi_foldbin_threshold_budget_logphi_jump_maxFiberExponent := by rw [hcommon]
      _ = 2 := by field_simp [hmax_ne]
  · exact D.xi_foldbin_threshold_budget_logphi_jump_lowerSlope_eq
  · exact ⟨D.xi_foldbin_threshold_budget_logphi_jump_upperSlope_eq,
      D.xi_foldbin_threshold_budget_logphi_jump_lowerSlope_eq.trans
        D.xi_foldbin_threshold_budget_logphi_jump_upperSlope_eq.symm⟩

end

end Omega.Zeta
