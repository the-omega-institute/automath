import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open Filter Topology

namespace Omega.Zeta

/-- Paper label: `thm:xi-zm4-moment-kernel-residue-asymptotics`.

An exponentially accurate pole-coefficient asymptotic forces the logarithmic growth rate
`log rho`. -/
theorem xi_zm4_moment_kernel_residue_asymptotics_log_growth_from_exponential_error
    (a : ℕ → ℝ) (r rho C alpha B : ℝ) (hr : 0 < r ∧ r < 1) (hrho : rho = r⁻¹)
    (hC : 0 < C) (ha : 0 < alpha ∧ alpha < rho) (hB : 0 ≤ B)
    (hasymp : ∀ m : ℕ, |a m - C * rho ^ m| ≤ B * alpha ^ m)
    (hpos : ∀ m : ℕ, 0 < a m) :
    (∀ m : ℕ, |a m - C * rho ^ m| ≤ B * alpha ^ m) ∧
      ∀ eps : ℝ, 0 < eps → ∃ M : ℕ, ∀ m ≥ M,
        |Real.log (a m) / (m : ℝ) - Real.log rho| < eps := by
  refine ⟨hasymp, ?_⟩
  intro eps heps
  have hrho_pos : 0 < rho := by
    rw [hrho]
    exact inv_pos.mpr hr.1
  have hq_nonneg : 0 ≤ alpha / rho := div_nonneg ha.1.le hrho_pos.le
  have hq_lt_one : alpha / rho < 1 := (div_lt_one hrho_pos).2 ha.2
  have hq_tendsto :
      Tendsto (fun m : ℕ => (alpha / rho) ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq_lt_one
  have hrel_tendsto :
      Tendsto (fun m : ℕ => (B / C) * (alpha / rho) ^ m) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hq_tendsto
  have hrel_event :
      ∀ᶠ m : ℕ in atTop, (B / C) * (alpha / rho) ^ m ≤ (1 / 2 : ℝ) :=
    hrel_tendsto.eventually_le_const (by norm_num)
  let K₁ : ℝ := |Real.log (2 * C)|
  let K₂ : ℝ := |Real.log (C / 2)|
  have hK₁_tendsto : Tendsto (fun m : ℕ => K₁ / (m : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hK₂_tendsto : Tendsto (fun m : ℕ => K₂ / (m : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hK₁_event : ∀ᶠ m : ℕ in atTop, K₁ / (m : ℝ) < eps :=
    hK₁_tendsto.eventually_lt_const heps
  have hK₂_event : ∀ᶠ m : ℕ in atTop, K₂ / (m : ℝ) < eps :=
    hK₂_tendsto.eventually_lt_const heps
  refine eventually_atTop.mp ?_
  filter_upwards [hrel_event, eventually_ge_atTop 1, hK₁_event, hK₂_event] with
    m hrel hm hK₁ hK₂
  have hn_pos_nat : 0 < m := Nat.succ_le_iff.mp hm
  have hn_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr hn_pos_nat
  have hmain_pos : 0 < C * rho ^ m := mul_pos hC (pow_pos hrho_pos m)
  have herror_half : B * alpha ^ m ≤ (C * rho ^ m) / 2 := by
    have hratio :
        (B * alpha ^ m) / (C * rho ^ m) = (B / C) * (alpha / rho) ^ m := by
      rw [div_pow]
      field_simp [hC.ne', (pow_pos hrho_pos m).ne']
    have : (B * alpha ^ m) / (C * rho ^ m) ≤ (1 / 2 : ℝ) := by
      simpa [hratio] using hrel
    have hmul := (div_le_iff₀ hmain_pos).mp this
    linarith
  have herror_nonneg : 0 ≤ B * alpha ^ m := mul_nonneg hB (pow_nonneg ha.1.le m)
  have hbounds := abs_le.mp (hasymp m)
  have hlower : (C * rho ^ m) / 2 ≤ a m := by
    have hcore : C * rho ^ m - B * alpha ^ m ≤ a m := by
      linarith [herror_nonneg]
    linarith
  have hupper : a m ≤ 2 * (C * rho ^ m) := by
    have hcore : a m ≤ C * rho ^ m + B * alpha ^ m := by
      linarith
    linarith
  have hlower_pos : 0 < (C * rho ^ m) / 2 := by positivity
  have hlog_lower :
      Real.log ((C * rho ^ m) / 2) ≤ Real.log (a m) :=
    Real.log_le_log hlower_pos hlower
  have hlog_upper :
      Real.log (a m) ≤ Real.log (2 * (C * rho ^ m)) :=
    Real.log_le_log (hpos m) hupper
  have hlog_lower_eq :
      Real.log ((C * rho ^ m) / 2) = Real.log (C / 2) + (m : ℝ) * Real.log rho := by
    rw [show (C * rho ^ m) / 2 = (C / 2) * rho ^ m by ring]
    rw [Real.log_mul (by positivity) (by exact (pow_pos hrho_pos m).ne')]
    rw [Real.log_pow]
  have hlog_upper_eq :
      Real.log (2 * (C * rho ^ m)) = Real.log (2 * C) + (m : ℝ) * Real.log rho := by
    rw [show 2 * (C * rho ^ m) = (2 * C) * rho ^ m by ring]
    rw [Real.log_mul (by positivity) (by exact (pow_pos hrho_pos m).ne')]
    rw [Real.log_pow]
  have hlower_div :
      Real.log rho + Real.log (C / 2) / (m : ℝ) ≤ Real.log (a m) / (m : ℝ) := by
    have := div_le_div_of_nonneg_right hlog_lower hn_pos.le
    rw [hlog_lower_eq] at this
    field_simp [hn_pos.ne'] at this ⊢
    linarith
  have hupper_div :
      Real.log (a m) / (m : ℝ) ≤ Real.log rho + Real.log (2 * C) / (m : ℝ) := by
    have := div_le_div_of_nonneg_right hlog_upper hn_pos.le
    rw [hlog_upper_eq] at this
    field_simp [hn_pos.ne'] at this ⊢
    linarith
  have hupper_eps :
      Real.log (a m) / (m : ℝ) - Real.log rho < eps := by
    have hle : Real.log (a m) / (m : ℝ) - Real.log rho ≤
        Real.log (2 * C) / (m : ℝ) := by linarith
    have habs : Real.log (2 * C) / (m : ℝ) ≤ K₁ / (m : ℝ) := by
      exact div_le_div_of_nonneg_right (le_abs_self _) hn_pos.le
    exact lt_of_le_of_lt (hle.trans habs) hK₁
  have hlower_eps :
      -(eps) < Real.log (a m) / (m : ℝ) - Real.log rho := by
    have hle : -(Real.log (a m) / (m : ℝ) - Real.log rho) ≤
        -(Real.log (C / 2) / (m : ℝ)) := by linarith
    have habs : -(Real.log (C / 2) / (m : ℝ)) ≤ K₂ / (m : ℝ) := by
      have hneg : -Real.log (C / 2) ≤ K₂ := neg_le_abs _
      simpa [neg_div] using div_le_div_of_nonneg_right hneg hn_pos.le
    have : -(Real.log (a m) / (m : ℝ) - Real.log rho) < eps :=
      lt_of_le_of_lt (hle.trans habs) hK₂
    linarith
  exact abs_lt.mpr ⟨hlower_eps, hupper_eps⟩

end Omega.Zeta
