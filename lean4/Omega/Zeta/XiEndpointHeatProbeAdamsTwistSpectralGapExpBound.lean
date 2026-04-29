import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Concrete finite atomic data for the endpoint heat-probe spectral-gap estimate. The endpoint
atom has already been subtracted, so the remaining probe is summed over the complement. -/
structure XiEndpointHeatProbeAdamsTwistSpectralGapExpBoundData where
  n : ℕ
  endpoint : Fin n
  N : ℕ
  rStar : ℝ
  weight : Fin n → ℝ
  ratio : Fin n → ℝ
  xi_endpoint_heat_probe_adams_twist_spectral_gap_exp_bound_weight_nonneg :
    ∀ i : Fin n, 0 ≤ weight i
  xi_endpoint_heat_probe_adams_twist_spectral_gap_exp_bound_rStar_nonneg :
    0 ≤ rStar
  xi_endpoint_heat_probe_adams_twist_spectral_gap_exp_bound_ratio_nonneg :
    ∀ i : Fin n, 0 ≤ ratio i
  xi_endpoint_heat_probe_adams_twist_spectral_gap_exp_bound_ratio_le :
    ∀ i : Fin n, i ≠ endpoint → ratio i ≤ rStar

namespace XiEndpointHeatProbeAdamsTwistSpectralGapExpBoundData

/-- The non-endpoint contribution of a single atom to the endpoint probe. -/
def xi_endpoint_heat_probe_adams_twist_spectral_gap_exp_bound_integrand
    (D : XiEndpointHeatProbeAdamsTwistSpectralGapExpBoundData) (i : Fin D.n) : ℝ :=
  D.weight i * D.ratio i ^ D.N

/-- The endpoint atom has been removed, so the error term is the complement sum. -/
def xi_endpoint_heat_probe_adams_twist_spectral_gap_exp_bound_error
    (D : XiEndpointHeatProbeAdamsTwistSpectralGapExpBoundData) : ℝ :=
  Finset.sum (Finset.univ.erase D.endpoint)
    D.xi_endpoint_heat_probe_adams_twist_spectral_gap_exp_bound_integrand

/-- Total mass of the complement after the endpoint atom is subtracted. -/
def xi_endpoint_heat_probe_adams_twist_spectral_gap_exp_bound_complementMass
    (D : XiEndpointHeatProbeAdamsTwistSpectralGapExpBoundData) : ℝ :=
  Finset.sum (Finset.univ.erase D.endpoint) D.weight

/-- Uniform exponential bound obtained by dominating every complement atom by `rStar^N`. -/
def spectralGapExpBound (D : XiEndpointHeatProbeAdamsTwistSpectralGapExpBoundData) : Prop :=
  D.xi_endpoint_heat_probe_adams_twist_spectral_gap_exp_bound_error ≤
    D.xi_endpoint_heat_probe_adams_twist_spectral_gap_exp_bound_complementMass * D.rStar ^ D.N

lemma xi_endpoint_heat_probe_adams_twist_spectral_gap_exp_bound_integrand_le
    (D : XiEndpointHeatProbeAdamsTwistSpectralGapExpBoundData) {i : Fin D.n}
    (hi : i ∈ Finset.univ.erase D.endpoint) :
    D.xi_endpoint_heat_probe_adams_twist_spectral_gap_exp_bound_integrand i ≤
      D.weight i * D.rStar ^ D.N := by
  rcases Finset.mem_erase.mp hi with ⟨hi_ne, _⟩
  unfold xi_endpoint_heat_probe_adams_twist_spectral_gap_exp_bound_integrand
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀
      (D.xi_endpoint_heat_probe_adams_twist_spectral_gap_exp_bound_ratio_nonneg i)
      (D.xi_endpoint_heat_probe_adams_twist_spectral_gap_exp_bound_ratio_le i hi_ne) D.N)
    (D.xi_endpoint_heat_probe_adams_twist_spectral_gap_exp_bound_weight_nonneg i)

lemma xi_endpoint_heat_probe_adams_twist_spectral_gap_exp_bound_proof
    (D : XiEndpointHeatProbeAdamsTwistSpectralGapExpBoundData) :
    D.spectralGapExpBound := by
  unfold spectralGapExpBound
  calc
    D.xi_endpoint_heat_probe_adams_twist_spectral_gap_exp_bound_error =
        Finset.sum (Finset.univ.erase D.endpoint)
          D.xi_endpoint_heat_probe_adams_twist_spectral_gap_exp_bound_integrand := rfl
    _ ≤ Finset.sum (Finset.univ.erase D.endpoint) (fun i => D.weight i * D.rStar ^ D.N) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact D.xi_endpoint_heat_probe_adams_twist_spectral_gap_exp_bound_integrand_le hi
    _ = D.xi_endpoint_heat_probe_adams_twist_spectral_gap_exp_bound_complementMass * D.rStar ^ D.N := by
          unfold xi_endpoint_heat_probe_adams_twist_spectral_gap_exp_bound_complementMass
          rw [Finset.sum_mul]

end XiEndpointHeatProbeAdamsTwistSpectralGapExpBoundData

open XiEndpointHeatProbeAdamsTwistSpectralGapExpBoundData

/-- Paper label: `cor:xi-endpoint-heat-probe-adams-twist-spectral-gap-exp-bound`. After removing
the limiting endpoint atom, each remaining probe term is bounded by `rStar^N`, so summing the
complement gives a uniform exponential error bound. -/
theorem paper_xi_endpoint_heat_probe_adams_twist_spectral_gap_exp_bound
    (D : XiEndpointHeatProbeAdamsTwistSpectralGapExpBoundData) :
    D.spectralGapExpBound := by
  exact D.xi_endpoint_heat_probe_adams_twist_spectral_gap_exp_bound_proof

end Omega.Zeta
