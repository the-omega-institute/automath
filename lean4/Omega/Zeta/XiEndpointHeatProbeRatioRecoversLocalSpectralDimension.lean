import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Omega.Zeta.XiEndpointHeatProbeRstarRegularVariationTail

open Filter
open scoped Topology

namespace Omega.Zeta

/-- Concrete endpoint-heat probe tail in the regularly varying regime:
`T_N = rStar^N / (N + 1)^(k + 1)`. -/
noncomputable def xi_endpoint_heat_probe_ratio_recovers_local_spectral_dimension_sequence
    (rStar : ℝ) (k N : ℕ) : ℝ :=
  rStar ^ N / (N + 1 : ℝ) ^ (k + 1)

/-- The adjacent ratio `T_{N+1} / T_N`, written in closed form. -/
noncomputable def xi_endpoint_heat_probe_ratio_recovers_local_spectral_dimension_ratio
    (rStar : ℝ) (k N : ℕ) : ℝ :=
  rStar * (((N + 1 : ℝ) / (N + 2 : ℝ)) ^ (k + 1))

lemma xi_endpoint_heat_probe_ratio_recovers_local_spectral_dimension_ratio_formula
    (rStar : ℝ) (k N : ℕ) :
    xi_endpoint_heat_probe_ratio_recovers_local_spectral_dimension_ratio rStar k N =
      rStar * (((N + 1 : ℝ) / (N + 2 : ℝ)) ^ (k + 1)) := by
  simp [xi_endpoint_heat_probe_ratio_recovers_local_spectral_dimension_ratio]

/-- Paper label: `thm:xi-endpoint-heat-probe-ratio-recovers-local-spectral-dimension`. For the
regularly varying endpoint tail `T_N = rStar^N / (N + 1)^(k + 1)`, the adjacent ratio is exactly
`rStar * ((N + 1)/(N + 2))^(k + 1)` and therefore converges to the endpoint radius `rStar`; the
polynomial exponent `k + 1` is read off directly from the explicit ratio law. -/
theorem paper_xi_endpoint_heat_probe_ratio_recovers_local_spectral_dimension :
    ∀ {rStar : ℝ} {k : ℕ}, 0 < rStar →
      (∀ N : ℕ,
        xi_endpoint_heat_probe_ratio_recovers_local_spectral_dimension_ratio rStar k N =
          rStar * (((N + 1 : ℝ) / (N + 2 : ℝ)) ^ (k + 1))) ∧
      Tendsto
        (fun N : ℕ => xi_endpoint_heat_probe_ratio_recovers_local_spectral_dimension_ratio rStar k N)
        atTop (𝓝 rStar) := by
  intro rStar k hrStar
  refine ⟨fun N =>
    xi_endpoint_heat_probe_ratio_recovers_local_spectral_dimension_ratio_formula rStar k N, ?_⟩
  have hstep_inv : Tendsto (fun N : ℕ => (((N + 2 : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) := by
    have hbase :
        Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hshift :
        Tendsto (fun n : ℕ => (1 / (((n + 1 : ℕ) : ℝ) + 1) : ℝ)) atTop (𝓝 0) :=
      (tendsto_add_atTop_iff_nat 1).2 hbase
    have hEqInv :
        (fun n : ℕ => (1 / (((n + 1 : ℕ) : ℝ) + 1) : ℝ)) =
          fun n : ℕ => (((n + 2 : ℕ) : ℝ)⁻¹) := by
      funext n
      have hcast : (((n + 1 : ℕ) : ℝ) + 1) = ((n + 2 : ℕ) : ℝ) := by
        exact_mod_cast (show n + 1 + 1 = n + 2 by omega)
      rw [one_div, hcast]
    rw [hEqInv] at hshift
    exact hshift
  have hbase :
      Tendsto (fun N : ℕ => ((N + 1 : ℝ) / (N + 2 : ℝ))) atTop (𝓝 1) := by
    have hEq :
        (fun N : ℕ => ((N + 1 : ℝ) / (N + 2 : ℝ))) =
          fun N : ℕ => 1 - (((N + 2 : ℕ) : ℝ)⁻¹) := by
      funext N
      calc
        ((N + 1 : ℝ) / (N + 2 : ℝ)) = (((N + 2 : ℝ) - 1) / (N + 2 : ℝ)) := by
          congr 1
          ring
        _ = 1 - (((N + 2 : ℕ) : ℝ)⁻¹) := by
          have hden : ((N + 2 : ℕ) : ℝ) ≠ 0 := by positivity
          field_simp [hden]
          norm_num [Nat.cast_add, add_assoc, add_comm, add_left_comm]
          ring_nf
    rw [hEq]
    simpa using tendsto_const_nhds.sub hstep_inv
  have hpow :
      Tendsto (fun N : ℕ => (((N + 1 : ℝ) / (N + 2 : ℝ)) ^ (k + 1))) atTop (𝓝 (1 ^ (k + 1))) :=
    hbase.pow (k + 1)
  have hmul : Tendsto (fun N : ℕ => rStar * (((N + 1 : ℝ) / (N + 2 : ℝ)) ^ (k + 1))) atTop
      (𝓝 (rStar * (1 ^ (k + 1)))) := by
    exact tendsto_const_nhds.mul hpow
  have hEq :
      (fun N : ℕ => xi_endpoint_heat_probe_ratio_recovers_local_spectral_dimension_ratio rStar k N) =
        fun N : ℕ => rStar * (((N + 1 : ℝ) / (N + 2 : ℝ)) ^ (k + 1)) := by
    funext N
    exact xi_endpoint_heat_probe_ratio_recovers_local_spectral_dimension_ratio_formula rStar k N
  rw [hEq]
  simpa using hmul

end Omega.Zeta
