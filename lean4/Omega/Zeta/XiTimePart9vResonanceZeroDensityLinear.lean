import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open Filter Topology

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part9v-resonance-zero-density-linear`. -/
theorem paper_xi_time_part9v_resonance_zero_density_linear
    (Nphi : ℝ → ℕ)
    (hlinear :
      ∃ C R0 : ℝ,
        0 ≤ C ∧
          1 ≤ R0 ∧
            ∀ R, R0 ≤ R → |(Nphi R : ℝ) - 2 * R| ≤ C * Real.log R) :
    Filter.Tendsto (fun R : ℝ => (Nphi R : ℝ) / (2 * R)) Filter.atTop (nhds 1) := by
  rcases hlinear with ⟨C, R0, hC, hR0, hbound⟩
  have hlog_div :
      Tendsto (fun R : ℝ => Real.log R / R) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
  have hupper :
      Tendsto (fun R : ℝ => (C / 2) * (Real.log R / R)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hlog_div :
      Tendsto (fun R : ℝ => (C / 2) * (Real.log R / R)) atTop (𝓝 ((C / 2) * 0)))
  have herror :
      Tendsto (fun R : ℝ => ((Nphi R : ℝ) - 2 * R) / (2 * R)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hupper
    filter_upwards [eventually_ge_atTop (max R0 1)] with R hR
    have hR0R : R0 ≤ R := le_trans (le_max_left R0 1) hR
    have hR1 : 1 ≤ R := le_trans (le_max_right R0 1) hR
    have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR1
    have hdenpos : 0 < 2 * R := mul_pos (by norm_num) hRpos
    have hdenabs : |2 * R| = 2 * R := abs_of_pos hdenpos
    have hboundR := hbound R hR0R
    calc
      ‖((Nphi R : ℝ) - 2 * R) / (2 * R)‖
          = |((Nphi R : ℝ) - 2 * R) / (2 * R)| := Real.norm_eq_abs _
      _ = |(Nphi R : ℝ) - 2 * R| / (2 * R) := by
        rw [abs_div, hdenabs]
      _ ≤ (C * Real.log R) / (2 * R) := by
        exact div_le_div_of_nonneg_right hboundR (le_of_lt hdenpos)
      _ = (C / 2) * (Real.log R / R) := by ring
  have hmain :
      Tendsto
        (fun R : ℝ => 1 + ((Nphi R : ℝ) - 2 * R) / (2 * R))
        atTop
        (𝓝 1) := by
    simpa using (tendsto_const_nhds.add herror :
      Tendsto
        (fun R : ℝ => 1 + ((Nphi R : ℝ) - 2 * R) / (2 * R))
        atTop
        (𝓝 (1 + 0)))
  apply hmain.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have hden_ne : 2 * R ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt hR)
  field_simp [hden_ne]
  ring

end Omega.Zeta
