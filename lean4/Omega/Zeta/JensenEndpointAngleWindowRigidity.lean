import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.JensenEndpointLocalization
import Omega.Zeta.JensenQuadraticResolutionBarrier

namespace Omega.Zeta

/-- Once the Jensen radius crosses the quadratic barrier, the endpoint localization package forces
the maximal height contribution to occur at the endpoint angle `θ = π`.
    cor:xi-jensen-endpoint-angle-window-rigidity -/
theorem paper_xi_jensen_endpoint_angle_window_rigidity (T δ0 rho theta : ℝ) (hδ0 : 0 ≤ δ0)
    (hρ : Omega.Zeta.mustExceedThreshold T δ0 rho) (hrho0 : 0 < rho) (hrho1 : rho < 1) :
    Omega.Zeta.quadraticBarrier T δ0 rho ∧
      ((1 - rho ^ 2) / (1 + rho ^ 2 + 2 * rho * Real.cos theta) ≤ (1 + rho) / (1 - rho)) ∧
      ((1 - rho ^ 2) / (1 + rho ^ 2 + 2 * rho * Real.cos Real.pi) = (1 + rho) / (1 - rho)) := by
  have hBarrier :=
    (paper_xi_jensen_quadratic_resolution_barrier T δ0 rho hδ0 hρ).2
  have hEndpoint :=
    Omega.TypedAddressBiaxialCompletion.paper_app_jensen_endpoint_localization
      (rho := rho) (theta := theta) hrho0 hrho1
  exact ⟨hBarrier, hEndpoint.1, hEndpoint.2⟩

end Omega.Zeta
