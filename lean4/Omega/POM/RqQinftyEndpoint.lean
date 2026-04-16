import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

open Filter Topology

namespace Omega.POM

set_option maxHeartbeats 400000 in
/-- Paper-facing endpoint wrapper for the collision-root scale `r_q^(1/q)`: if the standard
    max-fiber / moment bounds squeeze `r_q^(1/q)` between `√φ` and `√φ · φ^(1/q)`, then the
    endpoint limits for `r_q^(1/q)`, the normalized entropy rates, the Rényi dimensions, and the
    explicit `O(1/q)` error bound all follow.
    prop:pom-rq-qinfty-endpoint -/
theorem paper_pom_rq_qinfty_endpoint
    (rqRoot hq Dq : ℕ → ℝ)
    (hbound : ∀ q, 2 ≤ q →
      Real.sqrt Real.goldenRatio ≤ rqRoot q ∧
        rqRoot q ≤
          Real.sqrt Real.goldenRatio * Real.goldenRatio ^ ((1 : ℝ) / (q : ℝ)))
    (hhq : ∀ q, 2 ≤ q → hq q / (q : ℝ) = Real.log (2 / rqRoot q))
    (hDq : ∀ q, 2 ≤ q →
      Dq q = (hq q / ((q : ℝ) - 1)) * (Real.log Real.goldenRatio)⁻¹) :
    Tendsto rqRoot atTop (𝓝 (Real.sqrt Real.goldenRatio)) ∧
      Tendsto (fun q => hq q / (q : ℝ)) atTop (𝓝 (Real.log (2 / Real.sqrt Real.goldenRatio))) ∧
      Tendsto (fun q => hq q / ((q : ℝ) - 1))
        atTop (𝓝 (Real.log (2 / Real.sqrt Real.goldenRatio))) ∧
      Tendsto Dq atTop
        (𝓝 (Real.log (2 / Real.sqrt Real.goldenRatio) / Real.log Real.goldenRatio)) ∧
      ∀ q, 2 ≤ q →
        0 ≤ Real.log (2 / Real.sqrt Real.goldenRatio) - hq q / (q : ℝ) ∧
          Real.log (2 / Real.sqrt Real.goldenRatio) - hq q / (q : ℝ) ≤
            Real.log Real.goldenRatio / (q : ℝ) := by
  have hsqrt_pos : 0 < Real.sqrt Real.goldenRatio := Real.sqrt_pos_of_pos Real.goldenRatio_pos
  have hsqrt_ne : Real.sqrt Real.goldenRatio ≠ 0 := ne_of_gt hsqrt_pos
  have hpow :
      Tendsto (fun q : ℕ => Real.goldenRatio ^ ((1 : ℝ) / (q : ℝ))) atTop (𝓝 1) := by
    have hcont : ContinuousAt (fun x : ℝ => Real.goldenRatio ^ x) 0 :=
      Real.continuousAt_const_rpow Real.goldenRatio_pos.ne'
    have hinv : Tendsto (fun q : ℕ => ((q : ℝ)⁻¹)) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa [one_div] using hcont.tendsto.comp hinv
  have hupper :
      Tendsto (fun q : ℕ =>
        Real.sqrt Real.goldenRatio * Real.goldenRatio ^ ((1 : ℝ) / (q : ℝ)))
        atTop (𝓝 (Real.sqrt Real.goldenRatio)) := by
    simpa using (tendsto_const_nhds.mul hpow)
  have hrq :
      Tendsto rqRoot atTop (𝓝 (Real.sqrt Real.goldenRatio)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
    · exact (eventually_ge_atTop 2).mono fun q hq_ge => (hbound q hq_ge).1
    · exact (eventually_ge_atTop 2).mono fun q hq_ge => (hbound q hq_ge).2
  have herror :
      ∀ q, 2 ≤ q →
        0 ≤ Real.log (2 / Real.sqrt Real.goldenRatio) - hq q / (q : ℝ) ∧
          Real.log (2 / Real.sqrt Real.goldenRatio) - hq q / (q : ℝ) ≤
            Real.log Real.goldenRatio / (q : ℝ) := by
    intro q hq_ge
    have hrq_lower : Real.sqrt Real.goldenRatio ≤ rqRoot q := (hbound q hq_ge).1
    have hrq_upper :
        rqRoot q ≤
          Real.sqrt Real.goldenRatio * Real.goldenRatio ^ ((1 : ℝ) / (q : ℝ)) := (hbound q hq_ge).2
    have hrq_pos : 0 < rqRoot q := lt_of_lt_of_le hsqrt_pos hrq_lower
    have hrq_ne : rqRoot q ≠ 0 := ne_of_gt hrq_pos
    have hrpow_pos : 0 < Real.goldenRatio ^ ((1 : ℝ) / (q : ℝ)) :=
      Real.rpow_pos_of_pos Real.goldenRatio_pos _
    have hlog_lower : Real.log (Real.sqrt Real.goldenRatio) ≤ Real.log (rqRoot q) :=
      Real.log_le_log hsqrt_pos hrq_lower
    have hlog_upper : Real.log (rqRoot q) ≤
        Real.log (Real.sqrt Real.goldenRatio * Real.goldenRatio ^ ((1 : ℝ) / (q : ℝ))) := by
      exact Real.log_le_log hrq_pos hrq_upper
    have hupper_log :
        Real.log (Real.sqrt Real.goldenRatio * Real.goldenRatio ^ ((1 : ℝ) / (q : ℝ))) =
          Real.log (Real.sqrt Real.goldenRatio) + Real.log Real.goldenRatio / (q : ℝ) := by
      rw [Real.log_mul hsqrt_ne (ne_of_gt hrpow_pos), Real.log_rpow Real.goldenRatio_pos]
      ring
    have hhq' : hq q / (q : ℝ) = Real.log 2 - Real.log (rqRoot q) := by
      rw [hhq q hq_ge, Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hrq_ne]
    have htarget :
        Real.log (2 / Real.sqrt Real.goldenRatio) - hq q / (q : ℝ) =
          Real.log (rqRoot q) - Real.log (Real.sqrt Real.goldenRatio) := by
      rw [hhq', Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hsqrt_ne]
      ring
    constructor
    · rw [htarget]
      linarith
    · rw [htarget]
      rw [hupper_log] at hlog_upper
      linarith
  have herror_tendsto_zero :
      Tendsto (fun q : ℕ =>
        Real.log (2 / Real.sqrt Real.goldenRatio) - hq q / (q : ℝ)) atTop (𝓝 0) := by
    have hupper_zero :
        Tendsto (fun q : ℕ => Real.log Real.goldenRatio / (q : ℝ)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul
          (Real.log Real.goldenRatio)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper_zero ?_ ?_
    · exact (eventually_ge_atTop 2).mono fun q hq_ge => (herror q hq_ge).1
    · exact (eventually_ge_atTop 2).mono fun q hq_ge => (herror q hq_ge).2
  have hhq_limit :
      Tendsto (fun q : ℕ => hq q / (q : ℝ))
        atTop (𝓝 (Real.log (2 / Real.sqrt Real.goldenRatio))) := by
    have hconst :
        Tendsto (fun _ : ℕ => Real.log (2 / Real.sqrt Real.goldenRatio))
          atTop (𝓝 (Real.log (2 / Real.sqrt Real.goldenRatio))) :=
      tendsto_const_nhds
    have htmp :
        Tendsto
          (fun q : ℕ =>
            Real.log (2 / Real.sqrt Real.goldenRatio) -
              (Real.log (2 / Real.sqrt Real.goldenRatio) - hq q / (q : ℝ)))
          atTop
          (𝓝 (Real.log (2 / Real.sqrt Real.goldenRatio))) := by
      simpa using (hconst.sub herror_tendsto_zero)
    have heq :
        (fun q : ℕ =>
          Real.log (2 / Real.sqrt Real.goldenRatio) -
            (Real.log (2 / Real.sqrt Real.goldenRatio) - hq q / (q : ℝ))) =
          (fun q : ℕ => hq q / (q : ℝ)) := by
      funext q
      ring
    simpa [heq] using htmp
  have hratio :
      Tendsto (fun q : ℕ => (q : ℝ) / ((q : ℝ) - 1)) atTop (𝓝 1) := by
    have hsub :
        Tendsto (fun q : ℕ => (q : ℝ) - 1) atTop atTop := by
      simpa [sub_eq_add_neg] using
        tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_natCast_atTop_atTop
    have hinv :
        Tendsto (fun q : ℕ => ((q : ℝ) - 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hsub
    have hone :
        Tendsto (fun q : ℕ => 1 + ((q : ℝ) - 1)⁻¹) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.add hinv)
    have heq :
        (fun q : ℕ => (q : ℝ) / ((q : ℝ) - 1)) =ᶠ[atTop]
          (fun q : ℕ => 1 + ((q : ℝ) - 1)⁻¹) := by
      filter_upwards [eventually_ge_atTop 2] with q hq_ge
      have hq1 : (q : ℝ) - 1 ≠ 0 := by
        have : (1 : ℝ) < q := by exact_mod_cast hq_ge
        linarith
      field_simp [hq1]
      nlinarith
    exact hone.congr' heq.symm
  have hhq_over_limit :
      Tendsto (fun q : ℕ => hq q / ((q : ℝ) - 1))
        atTop (𝓝 (Real.log (2 / Real.sqrt Real.goldenRatio))) := by
    have hmul :
        Tendsto (fun q : ℕ =>
          ((q : ℝ) / ((q : ℝ) - 1)) * (hq q / (q : ℝ)))
          atTop (𝓝 (1 * Real.log (2 / Real.sqrt Real.goldenRatio))) := by
      exact hratio.mul hhq_limit
    have heq :
        (fun q : ℕ => hq q / ((q : ℝ) - 1)) =ᶠ[atTop]
          (fun q : ℕ => ((q : ℝ) / ((q : ℝ) - 1)) * (hq q / (q : ℝ))) := by
      filter_upwards [eventually_ge_atTop 2] with q hq_ge
      have hq0 : (q : ℝ) ≠ 0 := by positivity
      have hq1 : (q : ℝ) - 1 ≠ 0 := by
        have : (1 : ℝ) < q := by exact_mod_cast hq_ge
        linarith
      field_simp [hq0, hq1]
    simpa using hmul.congr' heq.symm
  have hDq_limit :
      Tendsto Dq atTop
        (𝓝 (Real.log (2 / Real.sqrt Real.goldenRatio) / Real.log Real.goldenRatio)) := by
    have hscaled :
        Tendsto (fun q : ℕ =>
          (hq q / ((q : ℝ) - 1)) * (Real.log Real.goldenRatio)⁻¹)
          atTop
          (𝓝
            (Real.log (2 / Real.sqrt Real.goldenRatio) / Real.log Real.goldenRatio)) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
        hhq_over_limit.const_mul ((Real.log Real.goldenRatio)⁻¹)
    have heq :
        Dq =ᶠ[atTop]
          (fun q : ℕ => (hq q / ((q : ℝ) - 1)) * (Real.log Real.goldenRatio)⁻¹) := by
      filter_upwards [eventually_ge_atTop 2] with q hq_ge
      exact hDq q hq_ge
    exact hscaled.congr' heq.symm
  exact ⟨hrq, hhq_limit, hhq_over_limit, hDq_limit, herror⟩

end Omega.POM
