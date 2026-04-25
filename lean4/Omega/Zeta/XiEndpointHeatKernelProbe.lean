import Mathlib.Order.Filter.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic

open Filter

namespace Omega.Zeta

/-- Concrete endpoint heat-kernel probe data. The Toeplitz quadratic form is identified with the
heat-kernel probe sequence, and that sequence is assumed antitone with a prescribed limit equal to
the endpoint atom mass. -/
structure xi_endpoint_heat_kernel_probe_data where
  toeplitzQuadraticForm : ℕ → ℝ
  heatKernelProbe : ℕ → ℝ
  endpointAtomMass : ℝ
  toeplitz_to_heatKernel :
    ∀ N : ℕ, toeplitzQuadraticForm N = heatKernelProbe N
  heatKernel_antitone : Antitone heatKernelProbe
  heatKernel_tendsto :
    Tendsto heatKernelProbe atTop (nhds endpointAtomMass)

namespace xi_endpoint_heat_kernel_probe_data

/-- The Toeplitz quadratic form equals the endpoint heat-kernel probe at every order. -/
def heat_kernel_identity
    (h : xi_endpoint_heat_kernel_probe_data) : Prop :=
  ∀ N : ℕ, h.toeplitzQuadraticForm N = h.heatKernelProbe N

/-- The endpoint probe decreases monotonically and converges to the endpoint atom mass. -/
def monotone_limit
    (h : xi_endpoint_heat_kernel_probe_data) : Prop :=
  Antitone h.heatKernelProbe ∧ Tendsto h.heatKernelProbe atTop (nhds h.endpointAtomMass)

end xi_endpoint_heat_kernel_probe_data

/-- Paper label: `thm:xi-endpoint-heat-kernel-probe`. The binomial Toeplitz quadratic form is
identified with the endpoint heat-kernel probe, and the packaged antitonicity together with the
recorded limit gives the endpoint atom mass. -/
theorem paper_xi_endpoint_heat_kernel_probe
    (h : xi_endpoint_heat_kernel_probe_data) :
    h.heat_kernel_identity /\ h.monotone_limit := by
  refine ⟨h.toeplitz_to_heatKernel, ?_⟩
  exact ⟨h.heatKernel_antitone, h.heatKernel_tendsto⟩

end Omega.Zeta
