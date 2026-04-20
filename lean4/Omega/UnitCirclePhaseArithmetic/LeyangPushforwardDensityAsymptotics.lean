import Mathlib

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

open Filter Set Topology

private def leyangDensityRatioEndpoint (t : ℝ) : ℝ :=
  (1 / (Real.pi * |t| * Real.sqrt (4 * |t| - 1))) /
    ((2 / Real.pi) / Real.sqrt (-(t + 1 / 4)))

private def leyangDensityRatioTail (t : ℝ) : ℝ :=
  (1 / (Real.pi * |t| * Real.sqrt (4 * |t| - 1))) /
    (1 / (2 * Real.pi * |t| * Real.sqrt |t|))

private lemma leyangDensityRatioEndpoint_eq (t : ℝ) (ht : t < -(1 : ℝ) / 4) :
    leyangDensityRatioEndpoint t = 1 / (4 * |t|) := by
  have ht0 : t < 0 := by linarith
  have harg : 0 ≤ 4 * |t| - 1 := by
    rw [abs_of_neg ht0]
    linarith
  have hsqrt :
      Real.sqrt (-(t + 1 / 4)) = Real.sqrt (4 * |t| - 1) / 2 := by
    have harg' : 0 ≤ 4 * (-t) - 1 := by linarith
    rw [abs_of_neg ht0]
    calc
      Real.sqrt (-(t + 1 / 4)) = Real.sqrt ((4 * (-t) - 1) / 4) := by congr; ring
      _ = Real.sqrt (4 * (-t) - 1) / Real.sqrt 4 := by
        rw [Real.sqrt_div harg' (4 : ℝ)]
      _ = Real.sqrt (4 * (-t) - 1) / 2 := by norm_num
  have hsqrt_ne : Real.sqrt (4 * |t| - 1) ≠ 0 := by
    rw [abs_of_neg ht0]
    apply Real.sqrt_ne_zero'.mpr
    linarith
  have habs_ne : |t| ≠ 0 := abs_ne_zero.mpr (by linarith [ht])
  rw [leyangDensityRatioEndpoint, hsqrt]
  field_simp [Real.pi_ne_zero, hsqrt_ne, habs_ne]
  field_simp [hsqrt_ne]
  norm_num

private lemma leyangDensityRatioTail_eq (t : ℝ) (ht : t < -(1 : ℝ) / 4) :
    leyangDensityRatioTail t = 2 / Real.sqrt (4 - 1 / |t|) := by
  have habs_pos : 0 < |t| := abs_pos.mpr (by linarith [ht])
  have harg_pos : 0 < 4 - 1 / |t| := by
    have habs_gt : (1 : ℝ) / 4 < |t| := by
      have ht0 : t < 0 := by linarith
      rw [abs_of_neg ht0]
      linarith
    have hdiv : (1 : ℝ) / |t| < 4 := by
      exact (div_lt_iff₀ habs_pos).2 (by nlinarith)
    linarith
  have hsqrt :
      Real.sqrt (4 * |t| - 1) = Real.sqrt |t| * Real.sqrt (4 - 1 / |t|) := by
    calc
      Real.sqrt (4 * |t| - 1) = Real.sqrt (|t| * (4 - 1 / |t|)) := by
        have habs_ne : |t| ≠ 0 := habs_pos.ne'
        congr 1
        field_simp [habs_ne]
      _ = Real.sqrt |t| * Real.sqrt (4 - 1 / |t|) := by
        rw [Real.sqrt_mul (abs_nonneg t)]
  have hsqrt_abs_ne : Real.sqrt |t| ≠ 0 := Real.sqrt_ne_zero'.mpr habs_pos
  have hsqrt_arg_ne : Real.sqrt (4 - 1 / |t|) ≠ 0 := Real.sqrt_ne_zero'.mpr harg_pos
  rw [leyangDensityRatioTail, hsqrt]
  field_simp [Real.pi_ne_zero, habs_pos.ne', hsqrt_abs_ne, hsqrt_arg_ne]

/-- Paper label: `cor:leyang-pushforward-density-asymptotics`. -/
theorem paper_leyang_pushforward_density_asymptotics :
    Tendsto
        (fun t : ℝ =>
          (1 / (Real.pi * |t| * Real.sqrt (4 * |t| - 1))) /
            ((2 / Real.pi) / Real.sqrt (-(t + 1 / 4))))
        (nhdsWithin (-(1 : ℝ) / 4) (Set.Iio (-(1 : ℝ) / 4))) (𝓝 1) ∧
      Tendsto
        (fun t : ℝ =>
          (1 / (Real.pi * |t| * Real.sqrt (4 * |t| - 1))) /
            (1 / (2 * Real.pi * |t| * Real.sqrt |t|)))
        atBot (𝓝 1) := by
  constructor
  · have hrewrite :
        leyangDensityRatioEndpoint =ᶠ[nhdsWithin (-(1 : ℝ) / 4) (Set.Iio (-(1 : ℝ) / 4))]
          fun t => 1 / (4 * |t|) := by
      refine Filter.eventuallyEq_of_mem self_mem_nhdsWithin ?_
      intro t ht
      exact leyangDensityRatioEndpoint_eq t ht
    have hbase : ContinuousAt (fun t : ℝ => 4 * |t|) (-(1 : ℝ) / 4) :=
      (continuous_const.mul continuous_abs).continuousAt
    have hcont : ContinuousAt (fun t : ℝ => 1 / (4 * |t|)) (-(1 : ℝ) / 4) := by
      simpa [one_div] using hbase.inv₀ (by norm_num)
    have hsimpl :
        Tendsto (fun t : ℝ => 1 / (4 * |t|))
          (nhdsWithin (-(1 : ℝ) / 4) (Set.Iio (-(1 : ℝ) / 4))) (𝓝 1) := by
      have hfull0 :
          Tendsto (fun t : ℝ => 1 / (4 * |t|)) (𝓝 (-(1 : ℝ) / 4))
            (𝓝 (1 / (4 * |(-(1 : ℝ) / 4)|))) := hcont.tendsto
      have hfull : Tendsto (fun t : ℝ => 1 / (4 * |t|)) (𝓝 (-(1 : ℝ) / 4)) (𝓝 1) := by
        have hval : (1 / (4 * |(-(1 : ℝ) / 4)|) : ℝ) = 1 := by
          norm_num
        simpa [hval] using hfull0
      exact hfull.mono_left inf_le_left
    exact hsimpl.congr' hrewrite.symm
  · have hrewrite :
        leyangDensityRatioTail =ᶠ[atBot] fun t => 2 / Real.sqrt (4 - 1 / |t|) := by
      refine Filter.eventuallyEq_of_mem (Iio_mem_atBot (-(1 : ℝ) / 4)) ?_
      intro t ht
      exact leyangDensityRatioTail_eq t ht
    have habs : Tendsto (fun t : ℝ => |t|) atBot atTop := tendsto_abs_atBot_atTop
    have hinv : Tendsto (fun t : ℝ => |t|⁻¹) atBot (𝓝 0) := by
      simpa [one_div] using habs.inv_tendsto_atTop
    have hsqrt : ContinuousAt (fun s : ℝ => Real.sqrt (4 - s)) 0 :=
      ((continuous_const.sub continuous_id).continuousAt).sqrt
    have hcont : ContinuousAt (fun s : ℝ => 2 / Real.sqrt (4 - s)) 0 := by
      have hinv_sqrt : ContinuousAt (fun s : ℝ => (Real.sqrt (4 - s))⁻¹) 0 := by
        exact hsqrt.inv₀ (by norm_num)
      simpa [div_eq_mul_inv] using continuousAt_const.mul hinv_sqrt
    have hsimpl : Tendsto (fun t : ℝ => 2 / Real.sqrt (4 - 1 / |t|)) atBot (𝓝 1) := by
      have hfull0 : Tendsto (fun t : ℝ => 2 / Real.sqrt (4 - |t|⁻¹)) atBot
          (𝓝 (2 / Real.sqrt 4)) := by
        simpa using hcont.tendsto.comp hinv
      have hval : (2 / Real.sqrt 4 : ℝ) = 1 := by
        norm_num
      simpa [one_div] using (hval ▸ hfull0)
    exact hsimpl.congr' hrewrite.symm

end

end Omega.UnitCirclePhaseArithmetic
