import Omega.Zeta.XiEndpointHeatProbeCyclotomicTargetExtraction

namespace Omega.Zeta

open scoped BigOperators
open Classical Filter Topology

noncomputable section

/-- The `d = 2`, `ω = 1` Adams-twist endpoint probe is exactly the half-angle specialization of
cyclotomic target extraction. The target set is the half-angle fiber `{± i}`, equivalently the
unit solutions of `z^2 = -1`, so the probe mass converges to the target mass.
    cor:xi-endpoint-heat-probe-adams-twist-halfangle -/
theorem paper_xi_endpoint_heat_probe_adams_twist_halfangle
    (S : Finset (Units Complex)) (μ : Units Complex → ℝ) (hμ : ∀ z, 0 ≤ μ z) :
    Tendsto (fun N : ℕ => xiEndpointHeatProbeCyclotomicMass S μ N 2 1) atTop
      (nhds (xiEndpointHeatProbeCyclotomicTargetMass S μ 2 1)) := by
  simpa using (paper_xi_endpoint_heat_probe_cyclotomic_target_extraction S μ 2 1 hμ).2

end

end Omega.Zeta
