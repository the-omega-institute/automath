import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.EndpointOddChebyshevIdentity

namespace Omega.UnitCirclePhaseArithmetic

/-- Paper-facing two-case endpoint jet regularization statement: even channels have vanishing
linear term, while odd channels have vanishing constant term. -/
def chebyshev_endpoint_jet_regularization_statement : Prop :=
  ∀ m : ℕ, ∀ g0 g1 S : ℝ,
    let jet :=
      g0 * (endpointChebyshevValue m : ℝ) + g1 * (endpointChebyshevDerivative m : ℝ) * S
    (Even m → jet = g0 * (endpointChebyshevValue m : ℝ)) ∧
      (¬ Even m → jet = g1 * (endpointChebyshevDerivative m : ℝ) * S)

/-- Paper label: `cor:chebyshev-endpoint-jet-regularization`. The previously formalized endpoint
derivative split forces even Chebyshev channels to lose their linear term at `S = 0`, while odd
channels lose their constant term and retain the first-order jet `g'(0) * C_m'(0) * S`. -/
theorem paper_chebyshev_endpoint_jet_regularization :
    chebyshev_endpoint_jet_regularization_statement := by
  intro m g0 g1 S
  dsimp
  rcases paper_chebyshev_endpoint_derivative_splitting m with ⟨_, hEven, hOdd⟩
  refine ⟨?_, ?_⟩
  · intro hm
    simp [hEven hm]
  · intro hm
    rcases hOdd hm with ⟨hValue, _⟩
    simp [hValue]

end Omega.UnitCirclePhaseArithmetic
