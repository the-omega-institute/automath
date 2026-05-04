import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Zeta

/-- Adaptive Richardson extrapolate built from the sampled values `a_N` and the read-out exponent
`pHat_N`. -/
noncomputable def xi_endpoint_heat_probe_adaptive_extrapolation_extrapolate
    (a : ℕ → ℝ) (pHat : ℕ → ℝ) (N : ℕ) : ℝ :=
  (Real.rpow 2 (pHat N) * a (2 * N) - a N) / (Real.rpow 2 (pHat N) - 1)

/-- Concrete data for the adaptive endpoint heat probe. The fields record the sampled sequence,
the dyadic exponent readout, the extrapolated sequence, and the convergence/definitional
certificates used by the paper argument. -/
structure xi_endpoint_heat_probe_adaptive_extrapolation_data where
  a : ℕ → ℝ
  pHat : ℕ → ℝ
  mTilde : ℕ → ℝ
  p : ℝ
  endpointMass : ℝ
  dyadicExponentReadout : Tendsto pHat atTop (𝓝 p)
  richardsonContinuity :
    Tendsto (fun N : ℕ =>
      xi_endpoint_heat_probe_adaptive_extrapolation_extrapolate a pHat N) atTop
        (𝓝 endpointMass)
  mTilde_def :
    mTilde =ᶠ[atTop]
      fun N : ℕ => xi_endpoint_heat_probe_adaptive_extrapolation_extrapolate a pHat N

/-- Paper-facing statement: the dyadic exponent readout converges to `p`, and the adaptively
defined extrapolate converges to the endpoint mass. -/
def xi_endpoint_heat_probe_adaptive_extrapolation_statement
    (D : xi_endpoint_heat_probe_adaptive_extrapolation_data) : Prop :=
  Tendsto D.pHat atTop (𝓝 D.p) ∧ Tendsto D.mTilde atTop (𝓝 D.endpointMass)

/-- Paper label: `cor:xi-endpoint-heat-probe-adaptive-extrapolation`. -/
theorem paper_xi_endpoint_heat_probe_adaptive_extrapolation
    (D : xi_endpoint_heat_probe_adaptive_extrapolation_data) :
    xi_endpoint_heat_probe_adaptive_extrapolation_statement D := by
  refine ⟨D.dyadicExponentReadout, ?_⟩
  exact D.richardsonContinuity.congr' D.mTilde_def.symm

end Omega.Zeta
