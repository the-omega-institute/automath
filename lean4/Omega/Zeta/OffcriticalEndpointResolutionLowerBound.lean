import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Omega.Zeta.OffcriticalQuadraticRadialCompression

namespace Omega.Zeta

open Omega.UnitCirclePhaseArithmetic

/-- Paper label: `thm:xi-offcritical-endpoint-resolution-lower-bound`.

The lower bound is valid in the regime `delta ∈ [delta0, 1 / 2]`, which is exactly the
off-critical range coming from `delta = 1 / 2 - β` with `β ∈ [0, 1 / 2 - delta0]`. -/
theorem paper_xi_offcritical_endpoint_resolution_lower_bound
    {γ δ delta0 T p : ℝ}
    (hdelta0 : 0 < delta0) (hdelta0_half : delta0 ≤ 1 / 2)
    (hdelta_lower : delta0 ≤ δ) (hdelta_upper : δ ≤ 1 / 2)
    (hT : 0 < T) (hγ : |γ| ≤ T) :
    let xi_offcritical_endpoint_resolution_lower_bound_margin :=
      4 * delta0 / (T ^ 2 + (1 + delta0) ^ 2)
    xi_offcritical_endpoint_resolution_lower_bound_margin ≤ appOffcriticalBoundaryDepth γ δ ∧
      (((2 : ℝ) ^ (-p) ≤ xi_offcritical_endpoint_resolution_lower_bound_margin) →
        Real.log ((T ^ 2 + (1 + delta0) ^ 2) / (4 * delta0)) ≤ p * Real.log 2) ∧
      Real.log ((T ^ 2 + (1 + delta0) ^ 2) / (4 * delta0)) =
        phasePrecisionPotential T + Real.log (1 / delta0) - Real.log (4 * Real.pi) -
          Real.log ((1 + T ^ 2) / (T ^ 2 + (1 + delta0) ^ 2)) := by
  dsimp
  have hdelta : 0 < δ := lt_of_lt_of_le hdelta0 hdelta_lower
  have hdepth :
      appOffcriticalBoundaryDepth γ δ = 4 * δ / (γ ^ 2 + (1 + δ) ^ 2) := by
    calc
      appOffcriticalBoundaryDepth γ δ = 4 * δ / (γ ^ 2 + (δ + 1) ^ 2) := by
        simpa using (paper_xi_offcritical_quadratic_radial_compression γ δ hdelta).1.2.2
      _ = 4 * δ / (γ ^ 2 + (1 + δ) ^ 2) := by ring_nf
  have hgamma_sq : γ ^ 2 ≤ T ^ 2 := by
    nlinarith [sq_abs γ, abs_nonneg γ, hγ]
  have hmargin_den_pos : 0 < T ^ 2 + (1 + delta0) ^ 2 := by positivity
  have hdepth_den_pos : 0 < γ ^ 2 + (1 + δ) ^ 2 := by positivity
  have hdelta_factor_nonneg : 0 ≤ γ ^ 2 + 1 - δ * delta0 := by
    nlinarith [sq_nonneg γ, hdelta_upper, hdelta0_half]
  have hmono_delta :
      delta0 * (γ ^ 2 + (1 + δ) ^ 2) ≤ δ * (γ ^ 2 + (1 + delta0) ^ 2) := by
    have haux : 0 ≤ (δ - delta0) * (γ ^ 2 + 1 - δ * delta0) := by
      nlinarith [hdelta_lower, hdelta_factor_nonneg]
    have haux_eq :
        δ * (γ ^ 2 + (1 + delta0) ^ 2) - delta0 * (γ ^ 2 + (1 + δ) ^ 2) =
          (δ - delta0) * (γ ^ 2 + 1 - δ * delta0) := by
      ring
    nlinarith [haux, haux_eq]
  have hmono_gamma :
      δ * (γ ^ 2 + (1 + delta0) ^ 2) ≤ δ * (T ^ 2 + (1 + delta0) ^ 2) := by
    nlinarith [hgamma_sq, hdelta]
  have hcross :
      (4 * delta0) * (γ ^ 2 + (1 + δ) ^ 2) ≤ (4 * δ) * (T ^ 2 + (1 + delta0) ^ 2) := by
    nlinarith [hmono_delta, hmono_gamma]
  have hmargin :
      4 * delta0 / (T ^ 2 + (1 + delta0) ^ 2) ≤ 4 * δ / (γ ^ 2 + (1 + δ) ^ 2) := by
    field_simp [hmargin_den_pos.ne', hdepth_den_pos.ne']
    nlinarith [hcross]
  have hdepthT :
      appOffcriticalBoundaryDepth T delta0 = 4 * delta0 / (T ^ 2 + (1 + delta0) ^ 2) := by
    calc
      appOffcriticalBoundaryDepth T delta0 = 4 * delta0 / (T ^ 2 + (delta0 + 1) ^ 2) := by
        simpa using (paper_xi_offcritical_quadratic_radial_compression T delta0 hdelta0).1.2.2
      _ = 4 * delta0 / (T ^ 2 + (1 + delta0) ^ 2) := by ring_nf
  have hfactor :
      appOffcriticalBoundaryDepth T delta0 =
        4 * Real.pi * delta0 * Real.exp (-phasePrecisionPotential T) *
          ((1 + T ^ 2) / (T ^ 2 + (1 + delta0) ^ 2)) := by
    simpa using (paper_xi_offcritical_quadratic_radial_compression T delta0 hdelta0).2.2
  have hratio_pos : 0 < ((1 + T ^ 2) / (T ^ 2 + (1 + delta0) ^ 2)) := by
    positivity
  have hprecision :
      -Real.log (appOffcriticalBoundaryDepth T delta0) =
        phasePrecisionPotential T + Real.log (1 / delta0) - Real.log (4 * Real.pi) -
          Real.log ((1 + T ^ 2) / (T ^ 2 + (1 + delta0) ^ 2)) := by
    have h4pi_ne : 4 * Real.pi ≠ 0 := by positivity
    have hdelta0_ne : delta0 ≠ 0 := ne_of_gt hdelta0
    have hexp_ne : Real.exp (-phasePrecisionPotential T) ≠ 0 := by positivity
    have hratio_ne : ((1 + T ^ 2) / (T ^ 2 + (1 + delta0) ^ 2)) ≠ 0 := ne_of_gt hratio_pos
    rw [hfactor]
    rw [Real.log_mul (show 4 * Real.pi * delta0 * Real.exp (-phasePrecisionPotential T) ≠ 0 by
      positivity) hratio_ne]
    rw [Real.log_mul (show 4 * Real.pi * delta0 ≠ 0 by positivity) hexp_ne]
    rw [Real.log_mul h4pi_ne hdelta0_ne]
    rw [Real.log_exp]
    have hdelta0_log : Real.log (1 / delta0) = -Real.log delta0 := by
      rw [one_div, Real.log_inv]
    have hdelta0_log' : Real.log delta0⁻¹ = -Real.log delta0 := by
      simpa only [one_div] using hdelta0_log
    ring_nf
    rw [hdelta0_log']
    ring
  refine ⟨by simpa [hdepth] using hmargin, ?_, ?_⟩
  · intro hdyad
    have hpow_pos : 0 < (2 : ℝ) ^ (-p) := Real.rpow_pos_of_pos (by norm_num) _
    have hlog :
        Real.log ((2 : ℝ) ^ (-p)) ≤
          Real.log (4 * delta0 / (T ^ 2 + (1 + delta0) ^ 2)) :=
      Real.log_le_log hpow_pos hdyad
    have hpow_log : Real.log ((2 : ℝ) ^ (-p)) = -p * Real.log 2 := by
      rw [Real.log_rpow (show 0 < (2 : ℝ) by norm_num)]
    have hfour_ne : 4 * delta0 ≠ 0 := by positivity
    have hmargin_den_ne : T ^ 2 + (1 + delta0) ^ 2 ≠ 0 := by positivity
    have hratio_inv :
        (T ^ 2 + (1 + delta0) ^ 2) / (4 * delta0) =
          (4 * delta0 / (T ^ 2 + (1 + delta0) ^ 2))⁻¹ := by
      field_simp [hfour_ne, hmargin_den_ne]
    rw [hpow_log] at hlog
    rw [hratio_inv, Real.log_inv]
    linarith
  · have hfour_ne : 4 * delta0 ≠ 0 := by positivity
    have hmargin_den_ne : T ^ 2 + (1 + delta0) ^ 2 ≠ 0 := by positivity
    have hratio_inv :
        (T ^ 2 + (1 + delta0) ^ 2) / (4 * delta0) =
          (4 * delta0 / (T ^ 2 + (1 + delta0) ^ 2))⁻¹ := by
      field_simp [hfour_ne, hmargin_den_ne]
    calc
      Real.log ((T ^ 2 + (1 + delta0) ^ 2) / (4 * delta0)) =
          -Real.log (4 * delta0 / (T ^ 2 + (1 + delta0) ^ 2)) := by
            rw [hratio_inv, Real.log_inv]
      _ = -Real.log (appOffcriticalBoundaryDepth T delta0) := by rw [hdepthT]
      _ =
          phasePrecisionPotential T + Real.log (1 / delta0) - Real.log (4 * Real.pi) -
            Real.log ((1 + T ^ 2) / (T ^ 2 + (1 + delta0) ^ 2)) := by
              exact hprecision

end Omega.Zeta
