import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- Concrete finite-alphabet KKT data for the diagonal-rate derivative calculation. -/
structure pom_diagonal_rate_frechet_derivative_scaling_potential_data where
  pom_diagonal_rate_frechet_derivative_scaling_potential_alphabetCard : ℕ
  pom_diagonal_rate_frechet_derivative_scaling_potential_direction :
    Fin pom_diagonal_rate_frechet_derivative_scaling_potential_alphabetCard → ℝ
  pom_diagonal_rate_frechet_derivative_scaling_potential_scalingPotential :
    Fin pom_diagonal_rate_frechet_derivative_scaling_potential_alphabetCard → ℝ
  pom_diagonal_rate_frechet_derivative_scaling_potential_gradient :
    Fin pom_diagonal_rate_frechet_derivative_scaling_potential_alphabetCard → ℝ
  pom_diagonal_rate_frechet_derivative_scaling_potential_frechetDerivative : ℝ
  pom_diagonal_rate_frechet_derivative_scaling_potential_kktMultiplier : ℝ
  pom_diagonal_rate_frechet_derivative_scaling_potential_tangent_direction :
    (∑ i : Fin pom_diagonal_rate_frechet_derivative_scaling_potential_alphabetCard,
      pom_diagonal_rate_frechet_derivative_scaling_potential_direction i) = 0
  pom_diagonal_rate_frechet_derivative_scaling_potential_envelope_identity :
    pom_diagonal_rate_frechet_derivative_scaling_potential_frechetDerivative =
      ∑ i : Fin pom_diagonal_rate_frechet_derivative_scaling_potential_alphabetCard,
        pom_diagonal_rate_frechet_derivative_scaling_potential_gradient i *
          pom_diagonal_rate_frechet_derivative_scaling_potential_direction i
  pom_diagonal_rate_frechet_derivative_scaling_potential_kkt_gradient_identity :
    ∀ i : Fin pom_diagonal_rate_frechet_derivative_scaling_potential_alphabetCard,
      pom_diagonal_rate_frechet_derivative_scaling_potential_gradient i =
        2 * pom_diagonal_rate_frechet_derivative_scaling_potential_scalingPotential i +
          pom_diagonal_rate_frechet_derivative_scaling_potential_kktMultiplier

namespace pom_diagonal_rate_frechet_derivative_scaling_potential_data

/-- Envelope derivative after quotienting out the constant KKT multiplier on the tangent
space of probability vectors. -/
def frechet_derivative_formula
    (D : pom_diagonal_rate_frechet_derivative_scaling_potential_data) : Prop :=
  D.pom_diagonal_rate_frechet_derivative_scaling_potential_frechetDerivative =
    2 * ∑ i : Fin D.pom_diagonal_rate_frechet_derivative_scaling_potential_alphabetCard,
      D.pom_diagonal_rate_frechet_derivative_scaling_potential_scalingPotential i *
        D.pom_diagonal_rate_frechet_derivative_scaling_potential_direction i

/-- The gradient is represented by twice the scaling potential modulo constants. -/
def gradient_mod_constants
    (D : pom_diagonal_rate_frechet_derivative_scaling_potential_data) : Prop :=
  ∃ c : ℝ,
    ∀ i : Fin D.pom_diagonal_rate_frechet_derivative_scaling_potential_alphabetCard,
      D.pom_diagonal_rate_frechet_derivative_scaling_potential_gradient i =
        2 * D.pom_diagonal_rate_frechet_derivative_scaling_potential_scalingPotential i + c

end pom_diagonal_rate_frechet_derivative_scaling_potential_data

/-- Paper label: `thm:pom-diagonal-rate-frechet-derivative-scaling-potential`. -/
theorem paper_pom_diagonal_rate_frechet_derivative_scaling_potential
    (D : pom_diagonal_rate_frechet_derivative_scaling_potential_data) :
    D.frechet_derivative_formula ∧ D.gradient_mod_constants := by
  have hsum :
      (∑ i : Fin D.pom_diagonal_rate_frechet_derivative_scaling_potential_alphabetCard,
        D.pom_diagonal_rate_frechet_derivative_scaling_potential_gradient i *
          D.pom_diagonal_rate_frechet_derivative_scaling_potential_direction i) =
        2 * ∑ i : Fin D.pom_diagonal_rate_frechet_derivative_scaling_potential_alphabetCard,
          D.pom_diagonal_rate_frechet_derivative_scaling_potential_scalingPotential i *
            D.pom_diagonal_rate_frechet_derivative_scaling_potential_direction i := by
    calc
      (∑ i : Fin D.pom_diagonal_rate_frechet_derivative_scaling_potential_alphabetCard,
        D.pom_diagonal_rate_frechet_derivative_scaling_potential_gradient i *
          D.pom_diagonal_rate_frechet_derivative_scaling_potential_direction i)
          =
          ∑ i : Fin D.pom_diagonal_rate_frechet_derivative_scaling_potential_alphabetCard,
            (2 * D.pom_diagonal_rate_frechet_derivative_scaling_potential_scalingPotential i +
              D.pom_diagonal_rate_frechet_derivative_scaling_potential_kktMultiplier) *
                D.pom_diagonal_rate_frechet_derivative_scaling_potential_direction i := by
            apply Finset.sum_congr rfl
            intro i _
            rw [D.pom_diagonal_rate_frechet_derivative_scaling_potential_kkt_gradient_identity i]
      _ =
          ∑ i : Fin D.pom_diagonal_rate_frechet_derivative_scaling_potential_alphabetCard,
            (2 *
              (D.pom_diagonal_rate_frechet_derivative_scaling_potential_scalingPotential i *
                D.pom_diagonal_rate_frechet_derivative_scaling_potential_direction i) +
              D.pom_diagonal_rate_frechet_derivative_scaling_potential_kktMultiplier *
                D.pom_diagonal_rate_frechet_derivative_scaling_potential_direction i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ =
          2 * ∑ i : Fin D.pom_diagonal_rate_frechet_derivative_scaling_potential_alphabetCard,
            D.pom_diagonal_rate_frechet_derivative_scaling_potential_scalingPotential i *
              D.pom_diagonal_rate_frechet_derivative_scaling_potential_direction i +
          D.pom_diagonal_rate_frechet_derivative_scaling_potential_kktMultiplier *
            ∑ i : Fin D.pom_diagonal_rate_frechet_derivative_scaling_potential_alphabetCard,
              D.pom_diagonal_rate_frechet_derivative_scaling_potential_direction i := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ =
          2 * ∑ i : Fin D.pom_diagonal_rate_frechet_derivative_scaling_potential_alphabetCard,
            D.pom_diagonal_rate_frechet_derivative_scaling_potential_scalingPotential i *
              D.pom_diagonal_rate_frechet_derivative_scaling_potential_direction i := by
            rw [D.pom_diagonal_rate_frechet_derivative_scaling_potential_tangent_direction]
            ring
  refine ⟨?_, ?_⟩
  · rw [pom_diagonal_rate_frechet_derivative_scaling_potential_data.frechet_derivative_formula,
      D.pom_diagonal_rate_frechet_derivative_scaling_potential_envelope_identity, hsum]
  · rw [pom_diagonal_rate_frechet_derivative_scaling_potential_data.gradient_mod_constants]
    refine ⟨D.pom_diagonal_rate_frechet_derivative_scaling_potential_kktMultiplier, ?_⟩
    intro i
    exact D.pom_diagonal_rate_frechet_derivative_scaling_potential_kkt_gradient_identity i

end

end Omega.POM
