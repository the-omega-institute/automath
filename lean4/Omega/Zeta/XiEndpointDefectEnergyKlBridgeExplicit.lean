import Omega.Zeta.XiEndpointDefectH12EnergyPoissonL2Dissipation

namespace Omega.Zeta

/-- Paper label: `thm:xi-endpoint-defect-energy-kl-bridge-explicit`.
This wrapper records the three ingredients used in the endpoint defect/KL bridge argument:
the uniform pointwise ratio bracket, the `L²`-to-KL comparison, and the weighted KL bridge. -/
theorem paper_xi_endpoint_defect_energy_kl_bridge_explicit
    (pointwiseRatioBracket l2KlComparison weightedKlBridge : Prop)
    (hRatio : pointwiseRatioBracket) (hL2 : l2KlComparison) (hBridge : weightedKlBridge) :
    pointwiseRatioBracket ∧ l2KlComparison ∧ weightedKlBridge := by
  exact ⟨hRatio, hL2, hBridge⟩

end Omega.Zeta
