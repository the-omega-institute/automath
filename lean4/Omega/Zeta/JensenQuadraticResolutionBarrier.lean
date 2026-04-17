import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega.Zeta

/-- Threshold radius coming from the quadratic resolution barrier. -/
noncomputable def jensenThresholdRadius (T δ0 : ℝ) : ℝ :=
  Real.sqrt (1 - 4 * δ0 / (T ^ 2 + (δ0 + 1) ^ 2))

/-- Any admissible radius must lie above the explicit threshold. -/
noncomputable def mustExceedThreshold (T δ0 ρ : ℝ) : Prop :=
  jensenThresholdRadius T δ0 < ρ

/-- Equivalent quadratic barrier written after solving for `1 - ρ²`. -/
noncomputable def quadraticBarrier (T δ0 ρ : ℝ) : Prop :=
  1 - ρ ^ 2 < 4 * δ0 / (T ^ 2 + (δ0 + 1) ^ 2)

lemma jensenThresholdRadicand_nonneg (T δ0 : ℝ) (hδ0 : 0 ≤ δ0) :
    0 ≤ 1 - 4 * δ0 / (T ^ 2 + (δ0 + 1) ^ 2) := by
  have hden_pos : 0 < T ^ 2 + (δ0 + 1) ^ 2 := by
    have hδ1 : 0 < δ0 + 1 := by linarith
    nlinarith [sq_nonneg T, sq_pos_of_pos hδ1]
  have hfrac_le :
      4 * δ0 / (T ^ 2 + (δ0 + 1) ^ 2) ≤ 1 := by
    have hmul : 4 * δ0 ≤ T ^ 2 + (δ0 + 1) ^ 2 := by
      nlinarith [sq_nonneg T, sq_nonneg (δ0 - 1)]
    have hnonneg : 0 ≤ 4 * δ0 := by nlinarith
    have hdiv :
        4 * δ0 / (T ^ 2 + (δ0 + 1) ^ 2) ≤ (T ^ 2 + (δ0 + 1) ^ 2) / (T ^ 2 + (δ0 + 1) ^ 2) := by
      exact div_le_div_of_nonneg_right hmul (le_of_lt hden_pos)
    rw [div_self hden_pos.ne'] at hdiv
    simpa using hdiv
  nlinarith

lemma one_sub_thresholdRadius_sq (T δ0 : ℝ) (hδ0 : 0 ≤ δ0) :
    1 - jensenThresholdRadius T δ0 ^ 2 = 4 * δ0 / (T ^ 2 + (δ0 + 1) ^ 2) := by
  unfold jensenThresholdRadius
  rw [Real.sq_sqrt (jensenThresholdRadicand_nonneg T δ0 hδ0)]
  ring

/-- If `ρ` lies above the threshold radius `R(T,δ₀)`, then the equivalent quadratic barrier holds:
`1 - ρ²` is strictly smaller than the explicit defect ratio.
    thm:xi-jensen-quadratic-resolution-barrier -/
theorem paper_xi_jensen_quadratic_resolution_barrier
    (T δ0 ρ : ℝ)
    (hδ0 : 0 ≤ δ0)
    (hρ : mustExceedThreshold T δ0 ρ) :
    mustExceedThreshold T δ0 ρ ∧ quadraticBarrier T δ0 ρ := by
  refine ⟨hρ, ?_⟩
  unfold mustExceedThreshold at hρ
  unfold quadraticBarrier
  have hR_nonneg : 0 ≤ jensenThresholdRadius T δ0 := Real.sqrt_nonneg _
  have hsq : jensenThresholdRadius T δ0 ^ 2 < ρ ^ 2 := by
    nlinarith [hρ, hR_nonneg]
  have hformula :
      1 - jensenThresholdRadius T δ0 ^ 2 = 4 * δ0 / (T ^ 2 + (δ0 + 1) ^ 2) :=
    one_sub_thresholdRadius_sq T δ0 hδ0
  nlinarith [hsq, hformula]

end Omega.Zeta
