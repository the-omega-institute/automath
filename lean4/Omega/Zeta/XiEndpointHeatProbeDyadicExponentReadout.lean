import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Filter
open scoped Topology

/-- Exact endpoint power-law model used for the dyadic readout. -/
noncomputable def xi_endpoint_heat_probe_dyadic_exponent_readout_profile
    (endpoint c : ℝ) (p N : ℕ) : ℝ :=
  if N = 0 then endpoint else endpoint + c / (N : ℝ) ^ p

/-- Three-level dyadic difference ratio for an endpoint heat probe. -/
noncomputable def xi_endpoint_heat_probe_dyadic_exponent_readout_ratio
    (endpoint c : ℝ) (p N : ℕ) : ℝ :=
  (xi_endpoint_heat_probe_dyadic_exponent_readout_profile endpoint c p N -
      xi_endpoint_heat_probe_dyadic_exponent_readout_profile endpoint c p (2 * N)) /
    (xi_endpoint_heat_probe_dyadic_exponent_readout_profile endpoint c p (2 * N) -
      xi_endpoint_heat_probe_dyadic_exponent_readout_profile endpoint c p (4 * N))

/-- Paper label: `cor:xi-endpoint-heat-probe-dyadic-exponent-readout`.
For the exact endpoint power law `endpoint + c N^{-p}`, the dyadic three-level ratio is
eventually the constant `2^p`; consequently the logarithmic readout returns `2p - 1`. -/
theorem paper_xi_endpoint_heat_probe_dyadic_exponent_readout (endpoint c : ℝ) (p : ℕ)
    (hp : 0 < p) (hc : c ≠ 0) :
    Tendsto
        (fun N : ℕ => xi_endpoint_heat_probe_dyadic_exponent_readout_ratio endpoint c p N)
        atTop (𝓝 ((2 : ℝ) ^ p)) ∧
      2 * (Real.log ((2 : ℝ) ^ p) / Real.log 2) - 1 = 2 * (p : ℝ) - 1 := by
  refine ⟨?_, ?_⟩
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    have h2N_nat : 2 * N ≠ 0 := Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hN)
    have h4N_nat : 4 * N ≠ 0 := Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hN)
    have h2N : ((2 * N : ℕ) : ℝ) = (2 : ℝ) * N := by norm_num
    have h4N : ((4 * N : ℕ) : ℝ) = (4 : ℝ) * N := by norm_num
    have hpowN : (N : ℝ) ^ p ≠ 0 := pow_ne_zero p hN0
    have hpow2 : ((2 : ℝ) ^ p) ≠ 0 := pow_ne_zero p (by norm_num)
    have hpow_ne_one : (2 : ℝ) ^ p ≠ 1 := by
      have hgt : (1 : ℝ) < (2 : ℝ) ^ p := one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hp)
      exact ne_of_gt hgt
    have hfactor : (1 - ((2 : ℝ) ^ p)⁻¹) ≠ 0 := by
      intro h
      have : ((2 : ℝ) ^ p)⁻¹ = 1 := by linarith
      have hone : (2 : ℝ) ^ p = 1 := by
        field_simp [hpow2] at this
        linarith
      exact hpow_ne_one hone
    symm
    rw [xi_endpoint_heat_probe_dyadic_exponent_readout_ratio,
      xi_endpoint_heat_probe_dyadic_exponent_readout_profile,
      xi_endpoint_heat_probe_dyadic_exponent_readout_profile,
      xi_endpoint_heat_probe_dyadic_exponent_readout_profile]
    simp [Nat.ne_of_gt hN, h2N_nat, h4N_nat, h2N, h4N, mul_pow]
    rw [show (4 : ℝ) ^ p = ((2 : ℝ) ^ p) ^ 2 by
      calc
        (4 : ℝ) ^ p = ((2 : ℝ) ^ 2) ^ p := by norm_num
        _ = (2 : ℝ) ^ (2 * p) := by rw [pow_mul]
        _ = (2 : ℝ) ^ (p * 2) := by rw [Nat.mul_comm]
        _ = ((2 : ℝ) ^ p) ^ 2 := by rw [pow_mul]]
    field_simp [hpowN, hpow2, hc, hfactor]
    have hdenq' : (2 : ℝ) ^ p - 1 ≠ 0 := by
      intro h
      apply hpow_ne_one
      linarith
    exact div_self hdenq'
  · have hlog2 : Real.log (2 : ℝ) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
    rw [Real.log_pow]
    field_simp [hlog2]

end Omega.Zeta
