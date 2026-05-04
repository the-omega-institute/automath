import Mathlib

open Filter
open scoped Topology

namespace Omega.Conclusion

noncomputable section

lemma conclusion_realinput40_uv_positive_branch_golden_limit_sqrt_normalize
    {s : ℝ} (hs : 1 < s) :
    Real.sqrt (5 * s ^ 4 - 6 * s ^ 3 - s ^ 2 + 2 * s + 1) =
      s ^ 2 *
        Real.sqrt (5 - 6 * s⁻¹ - (s ^ 2)⁻¹ + 2 * (s ^ 3)⁻¹ + (s ^ 4)⁻¹) := by
  have hs_ne : s ≠ 0 := by linarith
  have hpoly :
      5 * s ^ 4 - 6 * s ^ 3 - s ^ 2 + 2 * s + 1 =
        (s ^ 2) ^ 2 *
          (5 - 6 * s⁻¹ - (s ^ 2)⁻¹ + 2 * (s ^ 3)⁻¹ + (s ^ 4)⁻¹) := by
    field_simp [hs_ne]
  rw [hpoly, Real.sqrt_mul (sq_nonneg (s ^ 2))]
  have hsqrt : Real.sqrt ((s ^ 2) ^ 2) = s ^ 2 := by
    simpa using Real.sqrt_sq (sq_nonneg s)
  rw [hsqrt]

lemma conclusion_realinput40_uv_positive_branch_golden_limit_eventual_eq :
    (fun s : ℝ =>
        (s ^ 2 - s - 1 +
            Real.sqrt (5 * s ^ 4 - 6 * s ^ 3 - s ^ 2 + 2 * s + 1)) /
          (2 * (s ^ 2 - s))) =ᶠ[atTop]
      (fun s : ℝ =>
        (1 - s⁻¹ - (s ^ 2)⁻¹ +
            Real.sqrt (5 - 6 * s⁻¹ - (s ^ 2)⁻¹ + 2 * (s ^ 3)⁻¹ + (s ^ 4)⁻¹)) /
          (2 * (1 - s⁻¹))) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with s hs
  have hs_ne : s ≠ 0 := by linarith
  have hs_sub_ne : s ^ 2 - s ≠ 0 := by
    have hs_pos : 0 < s := by linarith
    nlinarith [mul_pos hs_pos (sub_pos.mpr hs)]
  have hs_one_sub_ne : 1 - s⁻¹ ≠ 0 := by
    intro h
    have hmul := congrArg (fun x : ℝ => x * s) h
    field_simp [hs_ne] at hmul
    nlinarith
  rw [conclusion_realinput40_uv_positive_branch_golden_limit_sqrt_normalize hs]
  field_simp [hs_ne, hs_sub_ne, hs_one_sub_ne]

lemma conclusion_realinput40_uv_positive_branch_golden_limit_normalized_tendsto :
    Tendsto
      (fun s : ℝ =>
        (1 - s⁻¹ - (s ^ 2)⁻¹ +
            Real.sqrt (5 - 6 * s⁻¹ - (s ^ 2)⁻¹ + 2 * (s ^ 3)⁻¹ + (s ^ 4)⁻¹)) /
          (2 * (1 - s⁻¹)))
      atTop (nhds ((1 + Real.sqrt 5) / 2)) := by
  have hinv1 : Tendsto (fun s : ℝ => s⁻¹) atTop (nhds (0 : ℝ)) :=
    tendsto_inv_atTop_zero
  have hpow2 : Tendsto (fun s : ℝ => s ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have hpow3 : Tendsto (fun s : ℝ => s ^ 3) atTop atTop :=
    tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)
  have hpow4 : Tendsto (fun s : ℝ => s ^ 4) atTop atTop :=
    tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)
  have hinv2 : Tendsto (fun s : ℝ => (s ^ 2)⁻¹) atTop (nhds (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hpow2
  have hinv3 : Tendsto (fun s : ℝ => (s ^ 3)⁻¹) atTop (nhds (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hpow3
  have hinv4 : Tendsto (fun s : ℝ => (s ^ 4)⁻¹) atTop (nhds (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hpow4
  have h6 : Tendsto (fun s : ℝ => (6 : ℝ) * s⁻¹) atTop (nhds (0 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (6 : ℝ))).mul hinv1
  have h2 : Tendsto (fun s : ℝ => (2 : ℝ) * (s ^ 3)⁻¹) atTop (nhds (0 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).mul hinv3
  have hinner :
      Tendsto
        (fun s : ℝ => 5 - 6 * s⁻¹ - (s ^ 2)⁻¹ + 2 * (s ^ 3)⁻¹ + (s ^ 4)⁻¹)
        atTop (nhds (5 : ℝ)) := by
    have hbase :
        Tendsto (fun s : ℝ => (5 : ℝ) - 6 * s⁻¹) atTop (nhds (5 - 0 : ℝ)) := by
      exact (tendsto_const_nhds (x := (5 : ℝ))).sub h6
    have hsub2 :
        Tendsto (fun s : ℝ => (5 : ℝ) - 6 * s⁻¹ - (s ^ 2)⁻¹)
          atTop (nhds (5 - 0 - 0 : ℝ)) := by
      exact hbase.sub hinv2
    have hadd3 :
        Tendsto (fun s : ℝ => (5 : ℝ) - 6 * s⁻¹ - (s ^ 2)⁻¹ + 2 * (s ^ 3)⁻¹)
          atTop (nhds (5 - 0 - 0 + 0 : ℝ)) := by
      exact hsub2.add h2
    have hadd4 :
        Tendsto
          (fun s : ℝ => (5 : ℝ) - 6 * s⁻¹ - (s ^ 2)⁻¹ +
            2 * (s ^ 3)⁻¹ + (s ^ 4)⁻¹)
          atTop (nhds (5 - 0 - 0 + 0 + 0 : ℝ)) := by
      exact hadd3.add hinv4
    simpa using hadd4
  have hsqrt :
      Tendsto
        (fun s : ℝ =>
          Real.sqrt (5 - 6 * s⁻¹ - (s ^ 2)⁻¹ + 2 * (s ^ 3)⁻¹ + (s ^ 4)⁻¹))
        atTop (nhds (Real.sqrt 5)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hinner
  have hnum :
      Tendsto
        (fun s : ℝ =>
          1 - s⁻¹ - (s ^ 2)⁻¹ +
            Real.sqrt (5 - 6 * s⁻¹ - (s ^ 2)⁻¹ + 2 * (s ^ 3)⁻¹ + (s ^ 4)⁻¹))
        atTop (nhds (1 + Real.sqrt 5)) := by
    have hbase :
        Tendsto (fun s : ℝ => (1 : ℝ) - s⁻¹) atTop (nhds (1 - 0 : ℝ)) := by
      exact (tendsto_const_nhds (x := (1 : ℝ))).sub hinv1
    have hsub2 :
        Tendsto (fun s : ℝ => (1 : ℝ) - s⁻¹ - (s ^ 2)⁻¹)
          atTop (nhds (1 - 0 - 0 : ℝ)) := by
      exact hbase.sub hinv2
    have hadd :
        Tendsto
          (fun s : ℝ =>
            (1 : ℝ) - s⁻¹ - (s ^ 2)⁻¹ +
              Real.sqrt (5 - 6 * s⁻¹ - (s ^ 2)⁻¹ + 2 * (s ^ 3)⁻¹ + (s ^ 4)⁻¹))
          atTop (nhds (1 - 0 - 0 + Real.sqrt 5 : ℝ)) := by
      exact hsub2.add hsqrt
    simpa using hadd
  have hden :
      Tendsto (fun s : ℝ => 2 * (1 - s⁻¹)) atTop (nhds (2 : ℝ)) := by
    have h :=
      (tendsto_const_nhds (x := (2 : ℝ))).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).sub hinv1)
    simpa using h
  have hden_ne : (2 : ℝ) ≠ 0 := by norm_num
  have hquot := hnum.div hden hden_ne
  simpa [add_comm, add_left_comm, add_assoc] using hquot

/-- Paper label: `thm:conclusion-realinput40-uv-positive-branch-golden-limit`. -/
theorem paper_conclusion_realinput40_uv_positive_branch_golden_limit :
    Tendsto
      (fun s : Real =>
        (s ^ 2 - s - 1 + Real.sqrt (5 * s ^ 4 - 6 * s ^ 3 - s ^ 2 + 2 * s + 1)) /
          (2 * (s ^ 2 - s)))
      atTop (nhds ((1 + Real.sqrt 5) / 2)) := by
  exact
    conclusion_realinput40_uv_positive_branch_golden_limit_normalized_tendsto.congr'
      conclusion_realinput40_uv_positive_branch_golden_limit_eventual_eq.symm

end

end Omega.Conclusion
