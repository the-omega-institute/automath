import Omega.UnitCirclePhaseArithmetic.EndpointOrthogonalDecomposition
import Omega.Zeta.XiEndpointTwoSymbolJet

namespace Omega.Zeta

open Omega.UnitCirclePhaseArithmetic

/-- Paper label: `cor:xi-endpoint-jet-orthogonal-decoupling`. -/
theorem paper_xi_endpoint_jet_orthogonal_decoupling (σ : ℝ) (g : Int → ℝ) :
    endpointRegularizedChannelOperator σ g = xiEndpointThreeChannelConstant σ g ∧
      xiEndpointTwoSymbolJetValue σ g =
        xiEndpointThreeChannelConstant σ g + xiEndpointChi4LinearTerm σ g := by
  let _ :=
    Omega.UnitCirclePhaseArithmetic.paper_endpoint_orthogonal_decomposition_z4_Rplus 1
      (by positivity)
  rcases paper_xi_endpoint_two_symbol_jet σ g with ⟨hconst, hjet, _, _, _, _, _⟩
  exact ⟨hconst, hjet⟩

end Omega.Zeta
