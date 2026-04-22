import Omega.UnitCirclePhaseArithmetic.UnitCircleComovingFirstOrder
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

/-- The dyadic bit threshold obtained by resolving the comoving endpoint margin. -/
noncomputable def unit_circle_comoving_bit_budget_threshold (δ : ℝ) : ℝ :=
  Real.logb 2 (((1 + δ) ^ 2) / (4 * δ))

/-- Paper label: `prop:unit-circle-comoving-bit-budget`. In the aligned chart `x₀ = γ`, the depth
law loses the height term, so the bit budget for separating endpoint residuals is controlled by the
single dyadic threshold attached to `δ`; if `δ` stays in `[δ₀, 1]`, this threshold is bounded by a
constant depending only on `δ₀`, not on `γ`. -/
theorem paper_unit_circle_comoving_bit_budget
    {δ₀ δ p γ : ℝ}
    (hδ₀ : 0 < δ₀) (hδ₀δ : δ₀ ≤ δ) (hδ_le_one : δ ≤ 1)
    (hres :
      (2 : ℝ) ^ (-p) ≤
        Omega.TypedAddressBiaxialCompletion.typedAddressComovingChartDepth δ γ γ) :
    unit_circle_comoving_bit_budget_threshold δ ≤ p ∧
      unit_circle_comoving_bit_budget_threshold δ ≤ Real.logb 2 (1 / δ₀) := by
  have hδ_nonneg : 0 ≤ δ := le_trans (le_of_lt hδ₀) hδ₀δ
  have hδ_pos : 0 < δ := lt_of_lt_of_le hδ₀ hδ₀δ
  have hfirst := paper_unit_circle_comoving_first_order (δ := δ) (γ := γ) hδ_nonneg
  have hdepth_eq :
      Omega.TypedAddressBiaxialCompletion.typedAddressComovingChartDepth δ γ γ =
        (4 * δ) / (1 + δ) ^ 2 := hfirst.2
  let unit_circle_comoving_bit_budget_budget_arg : ℝ := ((1 + δ) ^ 2) / (4 * δ)
  have hbudget_arg_pos : 0 < unit_circle_comoving_bit_budget_budget_arg := by
    dsimp [unit_circle_comoving_bit_budget_budget_arg]
    positivity
  have hbudget_mul :
      unit_circle_comoving_bit_budget_budget_arg *
        Omega.TypedAddressBiaxialCompletion.typedAddressComovingChartDepth δ γ γ = 1 := by
    rw [hdepth_eq]
    dsimp [unit_circle_comoving_bit_budget_budget_arg]
    field_simp [ne_of_gt hδ_pos, ne_of_gt (show 0 < (1 + δ) ^ 2 by positivity)]
  have hpow_pos : 0 < (2 : ℝ) ^ p := by
    exact Real.rpow_pos_of_pos (by norm_num) p
  have hbudget_le_pow : unit_circle_comoving_bit_budget_budget_arg ≤ (2 : ℝ) ^ p := by
    have hmul := mul_le_mul_of_nonneg_right hres hbudget_arg_pos.le
    have hpow_neg : (2 : ℝ) ^ (-p) = ((2 : ℝ) ^ p)⁻¹ := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    have hdiv :
        unit_circle_comoving_bit_budget_budget_arg / (2 : ℝ) ^ p ≤ 1 := by
      simpa [div_eq_mul_inv, hpow_neg, mul_assoc, mul_left_comm, mul_comm, hbudget_mul] using hmul
    simpa using (div_le_iff₀ hpow_pos).1 hdiv
  have hbudget_log :
      unit_circle_comoving_bit_budget_threshold δ ≤ p := by
    dsimp [unit_circle_comoving_bit_budget_threshold, unit_circle_comoving_bit_budget_budget_arg]
    have hlog :=
      Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hbudget_arg_pos hbudget_le_pow
    simpa [Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] using hlog
  have hbudget_const :
      unit_circle_comoving_bit_budget_budget_arg ≤ 1 / δ₀ := by
    dsimp [unit_circle_comoving_bit_budget_budget_arg]
    have hnum_le_four : (1 + δ) ^ 2 ≤ 4 := by
      nlinarith
    have hscaled₀ : δ₀ * (1 + δ) ^ 2 ≤ 4 * δ₀ := by
      nlinarith [hnum_le_four, le_of_lt hδ₀]
    have hscaled : δ₀ * (1 + δ) ^ 2 ≤ 4 * δ := by
      linarith
    have haux : (1 + δ) ^ 2 ≤ (4 * δ) / δ₀ := by
      exact (le_div_iff₀ hδ₀).2 (by simpa [mul_comm] using hscaled)
    have haux' : (1 + δ) ^ 2 ≤ (1 / δ₀) * (4 * δ) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using haux
    exact (div_le_iff₀ (show 0 < 4 * δ by positivity)).2 haux'
  have hbudget_log_const :
      unit_circle_comoving_bit_budget_threshold δ ≤ Real.logb 2 (1 / δ₀) := by
    dsimp [unit_circle_comoving_bit_budget_threshold, unit_circle_comoving_bit_budget_budget_arg]
    have hlog :=
      Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hbudget_arg_pos
        (by simpa using hbudget_const)
    simpa using hlog
  exact ⟨hbudget_log, hbudget_log_const⟩

end Omega.UnitCirclePhaseArithmetic
