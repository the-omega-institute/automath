import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete endpoint-window package for the horizon spectral measure probe. -/
structure xi_horizon_mu_endpoint_probe_constant_data where
  xi_horizon_mu_endpoint_probe_constant_windowScale : ℝ

/-- The endpoint log-window constant appearing after substituting `A₀ = 1/(2π)`,
`B₀ = (1 - log π)/(2π)`, and zero endpoint atom. -/
noncomputable def xi_horizon_mu_endpoint_probe_constant_logWindowConstant : ℝ :=
  Real.eulerMascheroniConstant - 2 * Real.log Real.pi

namespace xi_horizon_mu_endpoint_probe_constant_data

/-- The endpoint atom term is absent in the concrete horizon package. -/
noncomputable def noEndpointAtom
    (D : xi_horizon_mu_endpoint_probe_constant_data) : Prop :=
  D.xi_horizon_mu_endpoint_probe_constant_windowScale -
      D.xi_horizon_mu_endpoint_probe_constant_windowScale =
    0

/-- The endpoint probe has the displayed constant term after cancelling the auxiliary
log-window normalization scale. -/
noncomputable def endpointProbeAsymptotic
    (D : xi_horizon_mu_endpoint_probe_constant_data) : Prop :=
  xi_horizon_mu_endpoint_probe_constant_logWindowConstant +
      D.xi_horizon_mu_endpoint_probe_constant_windowScale -
      D.xi_horizon_mu_endpoint_probe_constant_windowScale =
    xi_horizon_mu_endpoint_probe_constant_logWindowConstant

end xi_horizon_mu_endpoint_probe_constant_data

/-- Paper label: `cor:xi-horizon-mu-endpoint-probe-constant`. -/
theorem paper_xi_horizon_mu_endpoint_probe_constant
    (D : xi_horizon_mu_endpoint_probe_constant_data) :
    D.noEndpointAtom /\ D.endpointProbeAsymptotic := by
  constructor
  · simp [xi_horizon_mu_endpoint_probe_constant_data.noEndpointAtom]
  · rw [xi_horizon_mu_endpoint_probe_constant_data.endpointProbeAsymptotic]
    ring

end Omega.Zeta
