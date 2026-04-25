import Mathlib.Tactic

open scoped Topology

namespace Omega.Zeta

/-- The real-variable residue left by the off-critical square-root pole.

Paper label: `prop:xi-gx-offcritical-pole-residue`. -/
theorem paper_xi_gx_offcritical_pole_residue (m : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    Filter.Tendsto
      (fun u : ℝ => (u - δ ^ 2) * ((m : ℝ) / (Real.sqrt u * (Real.sqrt u - δ))))
      (𝓝[>] (δ ^ 2)) (𝓝 (2 * (m : ℝ))) := by
  have hsqrt :
      Filter.Tendsto (fun u : ℝ => Real.sqrt u) (𝓝[>] (δ ^ 2)) (𝓝 δ) := by
    have hbase : Filter.Tendsto (fun u : ℝ => Real.sqrt u) (𝓝 (δ ^ 2))
        (𝓝 (Real.sqrt (δ ^ 2))) :=
      Real.continuous_sqrt.tendsto (δ ^ 2)
    have hwithin := hbase.mono_left (nhdsWithin_le_nhds : 𝓝[>] (δ ^ 2) ≤ 𝓝 (δ ^ 2))
    simpa [Real.sqrt_sq_eq_abs, abs_of_pos hδ] using hwithin
  have hlim :
      Filter.Tendsto (fun u : ℝ => (m : ℝ) * (Real.sqrt u + δ) / Real.sqrt u)
        (𝓝[>] (δ ^ 2)) (𝓝 (2 * (m : ℝ))) := by
    have hden : δ ≠ 0 := ne_of_gt hδ
    have hconst : Filter.Tendsto (fun _ : ℝ => δ) (𝓝[>] (δ ^ 2)) (𝓝 δ) :=
      tendsto_const_nhds
    have hquot :
        Filter.Tendsto (fun u : ℝ => (m : ℝ) * (Real.sqrt u + δ) / Real.sqrt u)
          (𝓝[>] (δ ^ 2)) (𝓝 ((m : ℝ) * (δ + δ) / δ)) :=
      ((hsqrt.add hconst).const_mul (m : ℝ)).div hsqrt hden
    convert hquot using 1
    field_simp [hden]
    ring_nf
  refine hlim.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with u hu
  have hu_gt : δ ^ 2 < u := hu
  have hu_nonneg : 0 ≤ u := le_trans (sq_nonneg δ) hu_gt.le
  have hsqrt_pos : 0 < Real.sqrt u := Real.sqrt_pos_of_pos (lt_of_le_of_lt (sq_nonneg δ) hu_gt)
  have hsqrt_ne : Real.sqrt u ≠ 0 := ne_of_gt hsqrt_pos
  have hsqrt_sub_ne : Real.sqrt u - δ ≠ 0 := by
    have hδ_lt_sqrt : δ < Real.sqrt u := by
      rw [← abs_of_pos hδ, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_lt_sqrt (sq_nonneg δ) hu_gt
    linarith
  have hsq : (Real.sqrt u) ^ 2 = u := Real.sq_sqrt hu_nonneg
  have hfactor : (Real.sqrt u - δ) * (Real.sqrt u + δ) = u - δ ^ 2 := by
    calc
      (Real.sqrt u - δ) * (Real.sqrt u + δ) = (Real.sqrt u) ^ 2 - δ ^ 2 := by ring_nf
      _ = u - δ ^ 2 := by rw [hsq]
  calc
    (m : ℝ) * (Real.sqrt u + δ) / Real.sqrt u =
        ((Real.sqrt u - δ) * (Real.sqrt u + δ)) *
          ((m : ℝ) / (Real.sqrt u * (Real.sqrt u - δ))) := by
      field_simp [hsqrt_ne, hsqrt_sub_ne]
    _ = (u - δ ^ 2) * ((m : ℝ) / (Real.sqrt u * (Real.sqrt u - δ))) := by
      rw [hfactor]

end Omega.Zeta
