import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.CircleDimension.EndpointFourChannelChi4
import Omega.CircleDimension.EndpointTristateSet
import Omega.Discussion.ChebyshevAdams
import Omega.UnitCirclePhaseArithmetic.EndpointDirichletSymbolWeights
import Omega.UnitCirclePhaseArithmetic.EndpointOddChebyshevIdentity

namespace Omega.Zeta

open Omega.CircleDimension
open Omega.Discussion
open Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- The constant three-channel term in the endpoint jet decomposition. -/
def xiEndpointThreeChannelConstant (σ : ℝ) (g : Int → ℝ) : ℝ :=
  endpointOddClassSum σ * g 0 +
    endpointZeroModFourClassSum σ * g 2 +
    endpointTwoModFourClassSum σ * g (-2)

/-- The `χ₄`-controlled linear correction carried by the two even symbols. -/
def xiEndpointChi4LinearTerm (σ : ℝ) (g : Int → ℝ) : ℝ :=
  σ * (endpointChi4 1 : ℝ) * (g 2 - g (-2))

/-- The paper-facing endpoint jet combining the constant three-channel term with the
`χ₄`-controlled linear correction. -/
def xiEndpointTwoSymbolJetValue (σ : ℝ) (g : Int → ℝ) : ℝ :=
  xiEndpointThreeChannelConstant σ g + xiEndpointChi4LinearTerm σ g

private theorem xi_endpoint_two_symbol_jet_assembly (σ : ℝ) (g : Int → ℝ) :
    xiEndpointTwoSymbolJetValue σ g =
      xiEndpointThreeChannelConstant σ g + xiEndpointChi4LinearTerm σ g := by
  rfl

/-- Concrete endpoint-jet package for the two-symbol reduction at the endpoint. -/
def XiEndpointTwoSymbolJet (σ : ℝ) (g : Int → ℝ) : Prop :=
  endpointRegularizedChannelOperator σ g = xiEndpointThreeChannelConstant σ g ∧
    xiEndpointTwoSymbolJetValue σ g =
      xiEndpointThreeChannelConstant σ g + xiEndpointChi4LinearTerm σ g ∧
    chebyAdams 0 0 = 2 ∧
    chebyAdams 0 0 = 2 * endpointChi4 1 ∧
    chebyAdams 1 0 = 0 ∧
    chebyAdams 2 0 = -2 ∧
    endpointChebyshevDerivative 1 = 1

/-- Paper label: `thm:xi-endpoint-two-symbol-jet`. -/
theorem paper_xi_endpoint_two_symbol_jet (σ : ℝ) (g : Int → ℝ) : XiEndpointTwoSymbolJet σ g := by
  have hconst := (paper_endpoint_dirichlet_symbol_weights σ g).1
  have hhalf : chebyAdams 0 0 = 2 := by
    simp [(paper_half_angle_z4_residue 0).2]
  have hchi : chebyAdams 0 0 = 2 * endpointChi4 1 := by
    simpa using paper_endpoint_four_channel_chi4 1 (by decide)
  have hodd : chebyAdams 1 0 = 0 := by
    exact (paper_endpoint_tristate_compression 1 (by decide)).1 (by norm_num)
  have htwo : chebyAdams 2 0 = -2 := by
    exact (paper_endpoint_tristate_compression 2 (by decide)).2.2 (by norm_num)
  have hderiv : endpointChebyshevDerivative 1 = 1 := by
    simpa [endpointQuarterTurnSign, endpointSecondKind] using
      (paper_chebyshev_endpoint_derivative_splitting 1).1
  exact ⟨hconst, xi_endpoint_two_symbol_jet_assembly σ g, hhalf, hchi, hodd, htwo, hderiv⟩

end

end Omega.Zeta
