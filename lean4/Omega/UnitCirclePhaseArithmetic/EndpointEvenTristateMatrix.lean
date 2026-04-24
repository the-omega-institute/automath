import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.EndpointZetaLChi4SymbolPair

namespace Omega.UnitCirclePhaseArithmetic

open Matrix

noncomputable section

/-- The endpoint even three-state input vector, ordered as `(0, +, -)`. -/
def endpointEvenTristateInput (g : Int → ℝ) : Fin 3 → ℝ :=
  ![g 0, g 2, g (-2)]

/-- The explicit endpoint even three-state matrix, written in channel-weight coordinates. -/
def endpointEvenTristateMatrix (σ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![endpointOddClassSum σ, endpointZeroModFourClassSum σ, endpointTwoModFourClassSum σ;
    0, endpointZetaSymbol (1 + σ), 0;
    0, endpointDyadicScale 2 σ * endpointZetaSymbol (1 + σ),
      (1 - endpointDyadicScale 2 σ) * endpointZetaSymbol (1 + σ)]

/-- Closed-form factorization of the endpoint even three-state matrix. -/
def endpointEvenTristateClosedMatrix (σ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  endpointZetaSymbol (1 + σ) •
    !![1 - endpointDyadicScale 2 σ, endpointDyadicScale 4 σ,
      endpointDyadicScale 2 σ - endpointDyadicScale 4 σ;
      0, 1, 0;
      0, endpointDyadicScale 2 σ, 1 - endpointDyadicScale 2 σ]

/-- The even three-state output vector after applying the endpoint matrix. -/
def endpointEvenTristateOutput (σ : ℝ) (g : Int → ℝ) : Fin 3 → ℝ :=
  endpointEvenTristateMatrix σ *ᵥ endpointEvenTristateInput g

/-- Coordinate package for the endpoint even three-state matrix action. -/
def EndpointEvenTristateMatrixStatement (σ : ℝ) (g : Int → ℝ) : Prop :=
  endpointEvenTristateMatrix σ = endpointEvenTristateClosedMatrix σ ∧
    endpointEvenTristateOutput σ g 0 = endpointRegularizedChannelOperator σ g ∧
    endpointEvenTristateOutput σ g 1 = endpointZetaSymbol (1 + σ) * g 2 ∧
    endpointEvenTristateOutput σ g 2 =
      endpointDyadicScale 2 σ * endpointZetaSymbol (1 + σ) * g 2 +
        (1 - endpointDyadicScale 2 σ) * endpointZetaSymbol (1 + σ) * g (-2)

/-- Paper label: `prop:endpoint-even-tristate-matrix`.
The three endpoint even channels form a closed `3`-state package, and the corresponding action
matrix is the stated explicit closed form. -/
  theorem paper_endpoint_even_tristate_matrix (σ : ℝ) (g : Int → ℝ) :
    EndpointEvenTristateMatrixStatement σ g := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [endpointEvenTristateMatrix, endpointEvenTristateClosedMatrix, endpointOddClassSum,
        endpointZeroModFourClassSum, endpointTwoModFourClassSum, mul_comm]
  · have hEven := (paper_endpoint_zeta_lchi4_symbol_pair σ g).1
    calc
      endpointEvenTristateOutput σ g 0 =
          endpointOddClassSum σ * g 0 +
            endpointZeroModFourClassSum σ * g 2 +
            endpointTwoModFourClassSum σ * g (-2) := by
        simp [endpointEvenTristateOutput, endpointEvenTristateMatrix, endpointEvenTristateInput,
          Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      _ = endpointRegularizedChannelOperator σ g := by
        simpa [endpointEvenSymbolDecomposition] using hEven.symm
  · simp [endpointEvenTristateOutput, endpointEvenTristateMatrix, endpointEvenTristateInput,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · simp [endpointEvenTristateOutput, endpointEvenTristateMatrix, endpointEvenTristateInput,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

end

end Omega.UnitCirclePhaseArithmetic
