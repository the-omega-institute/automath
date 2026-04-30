import Omega.Zeta.XiEndpointHeatProbePowerlawLeading
import Omega.Zeta.XiEndpointHeatProbeRichardsonExtrapolation

open Filter
open scoped Topology

namespace Omega.Zeta

/-- Paper label: `cor:xi-endpoint-heat-probe-powerlaw-coefficient-extraction`.
For the concrete power-law endpoint model, the dyadic tail difference extracts the leading
coefficient with the expected scale factor. -/
theorem paper_xi_endpoint_heat_probe_powerlaw_coefficient_extraction
    (mMinusOne KPlus KMinus : ℝ) (k : ℕ) :
    Tendsto
      (fun N : ℕ =>
        ((N + 1 : ℝ) ^ (k + 1)) *
          (xi_endpoint_heat_probe_powerlaw_leading_sequence mMinusOne KPlus KMinus k N -
            xi_endpoint_heat_probe_powerlaw_leading_sequence mMinusOne KPlus KMinus k (2 * N)))
      atTop
      (𝓝
        (xi_endpoint_heat_probe_powerlaw_leading_coefficient KPlus KMinus k *
          (1 - (1 : ℝ) / (2 : ℝ) ^ (k + 1)))) := by
  let C := xi_endpoint_heat_probe_powerlaw_leading_coefficient KPlus KMinus k
  have hsmall : Tendsto (fun N : ℕ => ((N + 1 : ℝ)⁻¹)) atTop (𝓝 (0 : ℝ)) := by
    simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hratio :
      Tendsto
        (fun N : ℕ => (N + 1 : ℝ) / (((2 * N + 1 : ℕ) : ℝ)))
        atTop (𝓝 ((1 : ℝ) / 2)) := by
    have hden_nat : Tendsto (fun N : ℕ => 2 * N + 1) atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro b
      refine ⟨b, ?_⟩
      intro N hN
      omega
    have hden_real :
        Tendsto (fun N : ℕ => (((2 * N + 1 : ℕ) : ℝ))) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hden_nat
    have hden_scaled :
        Tendsto (fun N : ℕ => (2 : ℝ) * (((2 * N + 1 : ℕ) : ℝ))) atTop atTop :=
      hden_real.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
    have hcorr :
        Tendsto (fun N : ℕ => ((2 : ℝ) * (((2 * N + 1 : ℕ) : ℝ)))⁻¹) atTop
          (𝓝 (0 : ℝ)) := by
      exact tendsto_inv_atTop_zero.comp hden_scaled
    have hsum :
        Tendsto
          (fun N : ℕ => (1 : ℝ) / 2 + ((2 : ℝ) * (((2 * N + 1 : ℕ) : ℝ)))⁻¹)
          atTop (𝓝 ((1 : ℝ) / 2 + 0)) :=
      tendsto_const_nhds.add hcorr
    have hsum' :
        Tendsto
          (fun N : ℕ => (1 : ℝ) / 2 + ((2 : ℝ) * (((2 * N + 1 : ℕ) : ℝ)))⁻¹)
          atTop (𝓝 ((1 : ℝ) / 2)) := by
      simpa using hsum
    refine hsum'.congr' ?_
    filter_upwards with N
    have hdenp : (((2 * N + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp [hdenp]
    norm_num [Nat.cast_add, Nat.cast_mul]
    ring
  have hpowl :
      Tendsto
        (fun N : ℕ => ((N + 1 : ℝ) / (((2 * N + 1 : ℕ) : ℝ))) ^ (k + 1))
        atTop (𝓝 ((1 : ℝ) / (2 : ℝ) ^ (k + 1))) := by
    have hpow := hratio.pow (k + 1)
    simpa [div_pow] using hpow
  have hlimit :
      Tendsto
        (fun N : ℕ =>
          C * (1 - ((N + 1 : ℝ) / (((2 * N + 1 : ℕ) : ℝ))) ^ (k + 1)))
        atTop (𝓝 (C * (1 - (1 : ℝ) / (2 : ℝ) ^ (k + 1)))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub hpowl)
  refine hlimit.congr' ?_
  filter_upwards with N
  have hN : ((N + 1 : ℝ) ^ (k + 1)) ≠ 0 := by positivity
  have h2N : ((((2 * N) + 1 : ℕ) : ℝ) ^ (k + 1)) ≠ 0 := by positivity
  symm
  calc
    ((N + 1 : ℝ) ^ (k + 1)) *
        (xi_endpoint_heat_probe_powerlaw_leading_sequence mMinusOne KPlus KMinus k N -
          xi_endpoint_heat_probe_powerlaw_leading_sequence mMinusOne KPlus KMinus k (2 * N))
        =
      ((N + 1 : ℝ) ^ (k + 1)) *
        (C / ((N + 1 : ℝ) ^ (k + 1)) -
        C / ((((2 * N) + 1 : ℕ) : ℝ) ^ (k + 1))) := by
        simp [xi_endpoint_heat_probe_powerlaw_leading_sequence,
          xiEndpointHeatProbeRegularVariationTerm, xiEndpointAtomMass, C]
    _ = C * (1 - ((N + 1 : ℝ) ^ (k + 1)) /
          ((((2 * N) + 1 : ℕ) : ℝ) ^ (k + 1))) := by
        field_simp [hN, h2N]
    _ = C * (1 - ((N + 1 : ℝ) / (((2 * N + 1 : ℕ) : ℝ))) ^ (k + 1)) := by
        rw [div_pow]

end Omega.Zeta
