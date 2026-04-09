import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Omega.Zeta.JensenSoftThresholdLowerBound

open Real Finset

/-- `log y ≥ 1 - 1/y` for `y ≥ 1`.
    con:xi-jensen-soft-threshold-depth-lower-bound -/
theorem log_ge_one_sub_inv (y : ℝ) (hy : 1 ≤ y) :
    1 - 1/y ≤ Real.log y := by
  have hypos : (0 : ℝ) < y := by linarith
  have hinvpos : (0 : ℝ) < y⁻¹ := inv_pos.mpr hypos
  have h1 : Real.log (y⁻¹) ≤ y⁻¹ - 1 := Real.log_le_sub_one_of_pos hinvpos
  rw [Real.log_inv] at h1
  have : (1 : ℝ) / y = y⁻¹ := one_div y
  linarith [h1, this]

/-- `log y ≥ (y-1)/y` for `y ≥ 1`.
    con:xi-jensen-soft-threshold-depth-lower-bound -/
theorem log_ge_sub_one_div (y : ℝ) (hy : 1 ≤ y) :
    (y - 1) / y ≤ Real.log y := by
  have hpos : (0 : ℝ) < y := by linarith
  have hne : y ≠ 0 := ne_of_gt hpos
  have heq : (y - 1) / y = 1 - 1/y := by field_simp
  rw [heq]
  exact log_ge_one_sub_inv y hy

/-- Single-index Jensen bound:
    `log(ϱ/a) ≥ (ϱ² - a²)/(2ϱ²)` when `0 < a < ϱ`.
    con:xi-jensen-soft-threshold-depth-lower-bound -/
theorem log_rho_div_a_lower_bound (ϱ a : ℝ) (hϱ : 0 < ϱ) (ha : 0 < a) (hlt : a < ϱ) :
    (ϱ^2 - a^2) / (2 * ϱ^2) ≤ Real.log (ϱ / a) := by
  -- Let y := ϱ²/a². Then y > 1, log(ρ/a) = (1/2)·log y, and log y ≥ 1 - 1/y.
  set y := ϱ^2 / a^2 with hy_def
  have ha2_pos : (0 : ℝ) < a^2 := by positivity
  have hϱ2_pos : (0 : ℝ) < ϱ^2 := by positivity
  have hy_pos : (0 : ℝ) < y := by
    simp only [hy_def]
    exact div_pos hϱ2_pos ha2_pos
  have hy_ge : 1 ≤ y := by
    simp only [hy_def]
    rw [le_div_iff₀ ha2_pos, one_mul]
    have hsq : a^2 ≤ ϱ^2 := by nlinarith [ha.le, hϱ.le, hlt.le]
    exact hsq
  have hlog_y : 1 - 1/y ≤ Real.log y := log_ge_one_sub_inv y hy_ge
  -- Express log y in terms of log(ϱ/a):
  have hdiv_pos : (0 : ℝ) < ϱ / a := div_pos hϱ ha
  have hsq_div : ϱ^2 / a^2 = (ϱ / a)^2 := by field_simp
  have hlog_y_eq : Real.log y = 2 * Real.log (ϱ / a) := by
    simp only [hy_def]
    rw [hsq_div, Real.log_pow]
    ring
  -- 1 - 1/y = (ϱ² - a²)/ϱ²
  have hone_sub : 1 - 1/y = (ϱ^2 - a^2) / ϱ^2 := by
    simp only [hy_def]
    have hane : a^2 ≠ 0 := ne_of_gt ha2_pos
    have hϱne : ϱ^2 ≠ 0 := ne_of_gt hϱ2_pos
    field_simp
  rw [hlog_y_eq] at hlog_y
  rw [hone_sub] at hlog_y
  -- Now: (ϱ² - a²)/ϱ² ≤ 2·log(ϱ/a); divide both sides by 2.
  have hϱ2_ne : (ϱ^2 : ℝ) ≠ 0 := ne_of_gt hϱ2_pos
  have heq2 : (ϱ^2 - a^2) / (2 * ϱ^2) = ((ϱ^2 - a^2) / ϱ^2) / 2 := by
    field_simp
  rw [heq2]
  linarith [hlog_y]

/-- Rearranged form: `ϱ² - a² ≤ 2·ϱ²·log(ϱ/a)` when `0 < a < ϱ`.
    con:xi-jensen-soft-threshold-depth-lower-bound -/
theorem two_rho_sq_log_rho_div_a_ge (ϱ a : ℝ) (hϱ : 0 < ϱ) (ha : 0 < a) (hlt : a < ϱ) :
    ϱ^2 - a^2 ≤ 2 * ϱ^2 * Real.log (ϱ / a) := by
  have h := log_rho_div_a_lower_bound ϱ a hϱ ha hlt
  have hϱsq : 0 < ϱ^2 := by positivity
  have h2ϱsq : 0 < 2 * ϱ^2 := by linarith
  have hmul : (ϱ^2 - a^2) / (2 * ϱ^2) * (2 * ϱ^2) ≤ Real.log (ϱ / a) * (2 * ϱ^2) :=
    mul_le_mul_of_nonneg_right h h2ϱsq.le
  rw [div_mul_cancel₀ _ (ne_of_gt h2ϱsq)] at hmul
  linarith [hmul]

/-- Jensen defect: sum of `log(ϱ/a k)` over indices where `a k < ϱ`.
    con:xi-jensen-soft-threshold-depth-lower-bound -/
noncomputable def jensenDefect {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a : ι → ℝ) (ϱ : ℝ) : ℝ :=
  ∑ k ∈ S.filter (fun k => a k < ϱ), Real.log (ϱ / a k)

/-- Soft-threshold squared gap sum.
    con:xi-jensen-soft-threshold-depth-lower-bound -/
noncomputable def softThresholdSum {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a : ι → ℝ) (ϱ : ℝ) : ℝ :=
  ∑ k ∈ S, max (ϱ^2 - (a k)^2) 0

/-- Jensen soft-threshold depth lower bound.
    con:xi-jensen-soft-threshold-depth-lower-bound -/
theorem jensen_soft_threshold_lower_bound
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (a : ι → ℝ) (ϱ : ℝ)
    (hϱ : 0 < ϱ) (ha : ∀ k ∈ S, 0 < a k) :
    (1 / (2 * ϱ^2)) * softThresholdSum S a ϱ ≤ jensenDefect S a ϱ := by
  have hϱ2 : (0 : ℝ) < ϱ^2 := by positivity
  have h2ϱ2 : (0 : ℝ) < 2 * ϱ^2 := by linarith
  -- Split the soft-threshold sum by the filter condition `a k < ϱ`.
  have hsplit :
      softThresholdSum S a ϱ =
        (∑ k ∈ S.filter (fun k => a k < ϱ), max (ϱ^2 - (a k)^2) 0) +
        (∑ k ∈ S.filter (fun k => ¬ a k < ϱ), max (ϱ^2 - (a k)^2) 0) := by
    unfold softThresholdSum
    exact (Finset.sum_filter_add_sum_filter_not S _ _).symm
  -- On the non-filter part (`a k ≥ ϱ`), the max is zero.
  have hnon_zero :
      (∑ k ∈ S.filter (fun k => ¬ a k < ϱ), max (ϱ^2 - (a k)^2) 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkS : k ∈ S := (Finset.mem_filter.mp hk).1
    have hge : ¬ a k < ϱ := (Finset.mem_filter.mp hk).2
    have hge' : ϱ ≤ a k := not_lt.mp hge
    have hak_pos : 0 < a k := ha k hkS
    have hsq_ge : ϱ^2 ≤ (a k)^2 := by nlinarith [hge', hϱ.le, hak_pos.le]
    exact max_eq_right (by linarith)
  rw [hsplit, hnon_zero, add_zero]
  -- On the filter part (`a k < ϱ`), max = ϱ² - (a k)².
  have hfilter_eq :
      (∑ k ∈ S.filter (fun k => a k < ϱ), max (ϱ^2 - (a k)^2) 0) =
        ∑ k ∈ S.filter (fun k => a k < ϱ), (ϱ^2 - (a k)^2) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkS : k ∈ S := (Finset.mem_filter.mp hk).1
    have hlt : a k < ϱ := (Finset.mem_filter.mp hk).2
    have hak_pos : 0 < a k := ha k hkS
    have hsq_lt : (a k)^2 < ϱ^2 := by nlinarith [hlt.le, hak_pos.le, hϱ.le]
    exact max_eq_left (by linarith)
  rw [hfilter_eq]
  -- Now need: (1/(2ϱ²)) · ∑ (ϱ² - a k²) ≤ ∑ log(ϱ/a k) on filter.
  unfold jensenDefect
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  rw [Finset.mem_filter] at hk
  obtain ⟨hkS, hlt⟩ := hk
  have hak_pos : 0 < a k := ha k hkS
  have hbnd := log_rho_div_a_lower_bound ϱ (a k) hϱ hak_pos hlt
  have heq : (1 / (2 * ϱ^2)) * (ϱ^2 - (a k)^2) =
      ((a k)^2 * 0 + (ϱ^2 - (a k)^2)) / (2 * ϱ^2) := by
    ring
  -- Direct rewrite: 1/(2ϱ²)·x = x/(2ϱ²)
  have : (1 / (2 * ϱ^2)) * (ϱ^2 - (a k)^2) = (ϱ^2 - (a k)^2) / (2 * ϱ^2) := by
    field_simp
  rw [this]
  exact hbnd

/-- Paper package: ξ Jensen soft-threshold depth lower bound.
    con:xi-jensen-soft-threshold-depth-lower-bound -/
theorem paper_xi_jensen_soft_threshold_depth_lower_bound
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (a : ι → ℝ) (ϱ : ℝ)
    (hϱ : 0 < ϱ) (ha : ∀ k ∈ S, 0 < a k) :
    (1 / (2 * ϱ^2)) * softThresholdSum S a ϱ ≤ jensenDefect S a ϱ :=
  jensen_soft_threshold_lower_bound S a ϱ hϱ ha

end Omega.Zeta.JensenSoftThresholdLowerBound
