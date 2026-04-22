import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- A concrete seed for the regularized zeta-symbol scale appearing in the endpoint formulas. -/
def endpointZetaSymbol (s : ℝ) : ℝ :=
  (Real.pi / 2) * Real.exp (s - 1)

/-- The dyadic scaling factor modeling the `b^{-(1+σ)}` contribution. -/
def endpointDyadicScale (b : ℕ) (σ : ℝ) : ℝ :=
  Real.exp (-(1 + σ) * Real.log b)

/-- Odd residue-class contribution to the endpoint regularized channel. -/
def endpointOddClassSum (σ : ℝ) : ℝ :=
  (1 - endpointDyadicScale 2 σ) * endpointZetaSymbol (1 + σ)

/-- `0 mod 4` residue-class contribution to the endpoint regularized channel. -/
def endpointZeroModFourClassSum (σ : ℝ) : ℝ :=
  endpointDyadicScale 4 σ * endpointZetaSymbol (1 + σ)

/-- `2 mod 4` residue-class contribution to the endpoint regularized channel. -/
def endpointTwoModFourClassSum (σ : ℝ) : ℝ :=
  (endpointDyadicScale 2 σ - endpointDyadicScale 4 σ) * endpointZetaSymbol (1 + σ)

/-- Endpoint regularized operator after splitting into the odd, `0 mod 4`, and `2 mod 4`
channels. -/
def endpointRegularizedChannelOperator (σ : ℝ) (g : Int → ℝ) : ℝ :=
  endpointOddClassSum σ * g 0 +
    endpointZeroModFourClassSum σ * g 2 +
    endpointTwoModFourClassSum σ * g (-2)

/-- The endpoint regularized operator splits into the odd / `0 mod 4` / `2 mod 4` channels, and
each channel is an explicit multiple of the common zeta-symbol factor.
    prop:endpoint-dirichlet-symbol-weights -/
theorem paper_endpoint_dirichlet_symbol_weights (σ : ℝ) (g : Int → ℝ) :
    endpointRegularizedChannelOperator σ g =
      endpointOddClassSum σ * g 0 +
        endpointZeroModFourClassSum σ * g 2 +
        endpointTwoModFourClassSum σ * g (-2) ∧
      endpointOddClassSum σ =
        (1 - endpointDyadicScale 2 σ) * endpointZetaSymbol (1 + σ) ∧
      endpointZeroModFourClassSum σ =
        endpointDyadicScale 4 σ * endpointZetaSymbol (1 + σ) ∧
      endpointTwoModFourClassSum σ =
        (endpointDyadicScale 2 σ - endpointDyadicScale 4 σ) * endpointZetaSymbol (1 + σ) := by
  simp [endpointRegularizedChannelOperator, endpointOddClassSum, endpointZeroModFourClassSum,
    endpointTwoModFourClassSum]

end

end Omega.UnitCirclePhaseArithmetic
