import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.EndpointEvenTristateMatrix

namespace Omega.UnitCirclePhaseArithmetic

open Matrix

noncomputable section

/-- The universal rank-one endpoint pole extracted from the even tristate package. -/
def endpointEvenPoleFunctional (g : Int → ℝ) : ℝ :=
  (1 / 2 : ℝ) * g 0 + (1 / 4 : ℝ) * g 2 + (1 / 4 : ℝ) * g (-2)

/-- The constant coefficient left after isolating the universal endpoint pole in the concrete
three-state model. -/
def endpointEvenFinitePartFunctional (g : Int → ℝ) : ℝ :=
  endpointZetaSymbol 1 * endpointEvenPoleFunctional g

/-- Concrete finite-part renormalization package for the endpoint even channels. At `σ = 0`, the
closed tristate matrix has the explicit pole row `(1/2, 1/4, 1/4)`, and the first output
coordinate is exactly the renormalized finite-part functional. -/
def endpointEvenFinitePartRenormalizationStatement : Prop :=
  endpointEvenTristateClosedMatrix 0 =
      endpointZetaSymbol 1 • !![(1 / 2 : ℝ), 1 / 4, 1 / 4;
        0, 1, 0;
        0, 1 / 2, 1 / 2] ∧
    ∀ g : Int → ℝ,
      endpointEvenPoleFunctional g =
        (1 / 2 : ℝ) * endpointEvenTristateInput g 0 +
          (1 / 4 : ℝ) * endpointEvenTristateInput g 1 +
          (1 / 4 : ℝ) * endpointEvenTristateInput g 2 ∧
      (endpointEvenTristateClosedMatrix 0 *ᵥ endpointEvenTristateInput g) 0 =
        endpointEvenFinitePartFunctional g ∧
      endpointEvenFinitePartFunctional g =
        endpointZetaSymbol 1 *
          ((1 / 2 : ℝ) * g 0 + (1 / 4 : ℝ) * g 2 + (1 / 4 : ℝ) * g (-2))

private lemma endpointDyadicScale_two_zero : endpointDyadicScale 2 0 = (1 / 2 : ℝ) := by
  calc
    endpointDyadicScale 2 0 = Real.exp (-Real.log 2) := by
      simp [endpointDyadicScale]
    _ = (Real.exp (Real.log 2))⁻¹ := by rw [Real.exp_neg]
    _ = (2 : ℝ)⁻¹ := by rw [Real.exp_log (by positivity : (0 : ℝ) < 2)]
    _ = (1 / 2 : ℝ) := by norm_num

private lemma endpointDyadicScale_four_zero : endpointDyadicScale 4 0 = (1 / 4 : ℝ) := by
  calc
    endpointDyadicScale 4 0 = Real.exp (-Real.log 4) := by
      simp [endpointDyadicScale]
    _ = (Real.exp (Real.log 4))⁻¹ := by rw [Real.exp_neg]
    _ = (4 : ℝ)⁻¹ := by rw [Real.exp_log (by positivity : (0 : ℝ) < 4)]
    _ = (1 / 4 : ℝ) := by norm_num

/-- Paper label: `thm:endpoint-even-finite-part-renormalization`. -/
theorem paper_endpoint_even_finite_part_renormalization :
    endpointEvenFinitePartRenormalizationStatement := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [endpointEvenTristateClosedMatrix, endpointDyadicScale_two_zero,
        endpointDyadicScale_four_zero, endpointZetaSymbol] <;> ring_nf
  · intro g
    refine ⟨?_, ?_, ?_⟩
    · simp [endpointEvenPoleFunctional, endpointEvenTristateInput]
    · simp [endpointEvenFinitePartFunctional, endpointEvenPoleFunctional,
        endpointEvenTristateClosedMatrix, endpointEvenTristateInput,
        endpointDyadicScale_two_zero, endpointDyadicScale_four_zero, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, endpointZetaSymbol] <;> ring_nf
    · rfl

end

end Omega.UnitCirclePhaseArithmetic
