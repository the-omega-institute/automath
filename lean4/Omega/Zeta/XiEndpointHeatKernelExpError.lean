import Mathlib.Topology.Basic
import Mathlib.Tactic
import Omega.Zeta.XiEndpointHeatKernelProbe

namespace Omega.Zeta

/-- Concrete endpoint heat-kernel error data.  The non-endpoint part is split into a closed
controlled support and a residual complement; the controlled part contracts by `q^(2N)`, and the
complement contributes its total mass. -/
structure xi_endpoint_heat_kernel_exp_error_data where
  Point : Type
  pointTopologicalSpace : TopologicalSpace Point
  endpoint : Point
  controlledSupport : Set Point
  controlledSupport_closed : IsClosed controlledSupport
  heatKernelProbe : ℕ → ℝ
  endpointAtomMass : ℝ
  controlledContribution : ℕ → ℝ
  complementContribution : ℕ → ℝ
  controlledMass : ℝ
  complementMass : ℝ
  contractionFactor : ℝ
  contractionFactor_pos : 0 < contractionFactor
  contractionFactor_lt_one : contractionFactor < 1
  endpoint_error_nonnegative :
    ∀ N : ℕ, 0 ≤ heatKernelProbe N - endpointAtomMass
  endpoint_error_split :
    ∀ N : ℕ,
      heatKernelProbe N - endpointAtomMass =
        controlledContribution N + complementContribution N
  controlledContribution_bound :
    ∀ N : ℕ,
      controlledContribution N ≤ contractionFactor ^ (2 * N) * controlledMass
  complementContribution_bound :
    ∀ N : ℕ, complementContribution N ≤ complementMass

attribute [instance] xi_endpoint_heat_kernel_exp_error_data.pointTopologicalSpace

namespace xi_endpoint_heat_kernel_exp_error_data

/-- Exponential endpoint-error bound after splitting the non-endpoint mass into the controlled
closed support and its complement. -/
def exp_error_bound (D : xi_endpoint_heat_kernel_exp_error_data) : Prop :=
  ∀ N : ℕ,
    0 ≤ D.heatKernelProbe N - D.endpointAtomMass ∧
      D.heatKernelProbe N - D.endpointAtomMass ≤
        D.contractionFactor ^ (2 * N) * D.controlledMass + D.complementMass

end xi_endpoint_heat_kernel_exp_error_data

/-- Paper label: `cor:xi-endpoint-heat-kernel-exp-error`. -/
theorem paper_xi_endpoint_heat_kernel_exp_error (D : xi_endpoint_heat_kernel_exp_error_data) :
    D.exp_error_bound := by
  intro N
  refine ⟨D.endpoint_error_nonnegative N, ?_⟩
  rw [D.endpoint_error_split N]
  exact add_le_add (D.controlledContribution_bound N) (D.complementContribution_bound N)

end Omega.Zeta
