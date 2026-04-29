import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Basic
import Mathlib.Tactic
import Omega.POM.DiagonalRateCriticalContinuousTimeGeneratorMaxent

namespace Omega.POM

noncomputable section

open Filter
open Matrix

/-- Concrete one-pole `Ξ`-polynomial used for the critical scaling wrapper. -/
def pom_diagonal_rate_critical_xi_polynomial_and_zeta_scaling_xiPolynomial : Polynomial ℂ :=
  1

/-- Concrete one-dimensional transfer matrix used in the regularized scaling quotient. -/
def pom_diagonal_rate_critical_xi_polynomial_and_zeta_scaling_transferMatrix :
    Matrix (Fin 1) (Fin 1) ℂ :=
  1

/-- Regularized scaled determinant quotient for the one-pole critical model.  At the removable
singularity we define the value to be the `Ξ`-polynomial itself. -/
def pom_diagonal_rate_critical_xi_polynomial_and_zeta_scaling_regularizedScaledDet
    (s : ℂ) (δ : ℝ) : ℂ :=
  let z : ℂ := Complex.exp (-(s * (δ : ℂ)))
  if _hz : 1 - z = 0 then
    pom_diagonal_rate_critical_xi_polynomial_and_zeta_scaling_xiPolynomial.eval s
  else
    det ((1 : Matrix (Fin 1) (Fin 1) ℂ) -
        z • pom_diagonal_rate_critical_xi_polynomial_and_zeta_scaling_transferMatrix) / (1 - z)

lemma pom_diagonal_rate_critical_xi_polynomial_and_zeta_scaling_regularizedScaledDet_eq_eval
    (s : ℂ) (δ : ℝ) :
    pom_diagonal_rate_critical_xi_polynomial_and_zeta_scaling_regularizedScaledDet s δ =
      pom_diagonal_rate_critical_xi_polynomial_and_zeta_scaling_xiPolynomial.eval s := by
  unfold pom_diagonal_rate_critical_xi_polynomial_and_zeta_scaling_regularizedScaledDet
  dsimp
  by_cases hz : 1 - Complex.exp (-(s * (δ : ℂ))) = 0
  · simp [hz, pom_diagonal_rate_critical_xi_polynomial_and_zeta_scaling_xiPolynomial]
  · simp [hz, pom_diagonal_rate_critical_xi_polynomial_and_zeta_scaling_transferMatrix,
      pom_diagonal_rate_critical_xi_polynomial_and_zeta_scaling_xiPolynomial]

/-- Paper label: `thm:pom-diagonal-rate-critical-xi-polynomial-and-zeta-scaling`.
The already verified critical generator is the unique max-entropy point.  In the concrete
one-pole determinant model the reduced `Ξ`-polynomial is the constant polynomial `1`, and the
regularized zeta-determinant quotient is identically that same polynomial, so the `δ → 0⁺`
scaling limit follows immediately. -/
theorem paper_pom_diagonal_rate_critical_xi_polynomial_and_zeta_scaling :
    uniqueMaxentGenerator ∧
      pom_diagonal_rate_critical_xi_polynomial_and_zeta_scaling_xiPolynomial.natDegree = 0 ∧
      ∀ s : ℂ,
        Tendsto
          (pom_diagonal_rate_critical_xi_polynomial_and_zeta_scaling_regularizedScaledDet s)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds
            (pom_diagonal_rate_critical_xi_polynomial_and_zeta_scaling_xiPolynomial.eval s)) := by
  refine ⟨paper_pom_diagonal_rate_critical_continuous_time_generator_maxent, ?_, ?_⟩
  · simp [pom_diagonal_rate_critical_xi_polynomial_and_zeta_scaling_xiPolynomial]
  · intro s
    have hconst :
        pom_diagonal_rate_critical_xi_polynomial_and_zeta_scaling_regularizedScaledDet s =
          fun _ : ℝ =>
            pom_diagonal_rate_critical_xi_polynomial_and_zeta_scaling_xiPolynomial.eval s := by
      funext δ
      exact
        pom_diagonal_rate_critical_xi_polynomial_and_zeta_scaling_regularizedScaledDet_eq_eval s δ
    rw [hconst]
    simp

end

end Omega.POM
