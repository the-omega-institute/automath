import Mathlib.Data.Real.Basic

namespace Omega.Zeta

/-- The endpoint Cauchy ledger identity obtained after specializing at `z = -r`. -/
def xi_endpoint_poisson_jensen_cauchy_ledger_statement
    (endpointRadius : ℝ) (poissonJensenLeft _poissonJensenBoundary _greenLedger : ℝ → ℝ)
    (cauchyBoundaryLedger : ℝ → ℝ) (endpointGreenLedger : ℝ) : Prop :=
  poissonJensenLeft (-endpointRadius) =
    cauchyBoundaryLedger endpointRadius + endpointGreenLedger

/-- Paper label: `thm:xi-endpoint-poisson-jensen-cauchy-ledger`. -/
theorem paper_xi_endpoint_poisson_jensen_cauchy_ledger
    (endpointRadius : ℝ) (poissonJensenLeft poissonJensenBoundary greenLedger : ℝ → ℝ)
    (cauchyBoundaryLedger : ℝ → ℝ) (endpointGreenLedger : ℝ)
    (poissonJensen_identity :
      ∀ z : ℝ, poissonJensenLeft z = poissonJensenBoundary z + greenLedger z)
    (cayley_pullback_boundary :
      poissonJensenBoundary (-endpointRadius) = cauchyBoundaryLedger endpointRadius)
    (endpoint_green_ledger : greenLedger (-endpointRadius) = endpointGreenLedger) :
    xi_endpoint_poisson_jensen_cauchy_ledger_statement endpointRadius poissonJensenLeft
      poissonJensenBoundary greenLedger cauchyBoundaryLedger endpointGreenLedger := by
  unfold xi_endpoint_poisson_jensen_cauchy_ledger_statement
  rw [poissonJensen_identity, cayley_pullback_boundary, endpoint_green_ledger]

end Omega.Zeta
