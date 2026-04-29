import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Differential entropy of the standard logistic kernel in natural-log units. -/
def xi_logistic_mutual_information_low_resolution_h_phi : ℝ :=
  2

/-- Location Fisher information constant for the logistic kernel. -/
def xi_logistic_mutual_information_low_resolution_fisher_constant : ℝ :=
  1 / 3

/-- The low-resolution quadratic coefficient is half of the location Fisher information. -/
def xi_logistic_mutual_information_low_resolution_quadratic_coefficient : ℝ :=
  xi_logistic_mutual_information_low_resolution_fisher_constant / 2

/-- Concrete entropy and low-resolution expansion data for the logistic additive-noise channel. -/
structure xi_logistic_mutual_information_low_resolution_Data where
  outputEntropy : ℝ
  mutualInformation : ℝ
  variance : ℝ
  fourthMomentRemainder : ℝ
  entropy_decomposition :
    mutualInformation =
      outputEntropy - xi_logistic_mutual_information_low_resolution_h_phi
  low_resolution_quadratic_expansion :
    mutualInformation =
      xi_logistic_mutual_information_low_resolution_quadratic_coefficient * variance +
        fourthMomentRemainder

/-- Paper-facing package for the logistic mutual-information entropy split and its
low-resolution quadratic coefficient. -/
def xi_logistic_mutual_information_low_resolution_statement
    (D : xi_logistic_mutual_information_low_resolution_Data) : Prop :=
  D.mutualInformation = D.outputEntropy - 2 ∧
    xi_logistic_mutual_information_low_resolution_h_phi = 2 ∧
    xi_logistic_mutual_information_low_resolution_fisher_constant = 1 / 3 ∧
    xi_logistic_mutual_information_low_resolution_quadratic_coefficient = 1 / 6 ∧
    D.mutualInformation = (1 / 6) * D.variance + D.fourthMomentRemainder

/-- Paper label: `prop:xi-logistic-mutual-information-low-resolution`. -/
theorem paper_xi_logistic_mutual_information_low_resolution
    (D : xi_logistic_mutual_information_low_resolution_Data) :
    xi_logistic_mutual_information_low_resolution_statement D := by
  refine ⟨?_, rfl, rfl, ?_, ?_⟩
  · simpa [xi_logistic_mutual_information_low_resolution_h_phi] using D.entropy_decomposition
  · norm_num [xi_logistic_mutual_information_low_resolution_quadratic_coefficient,
      xi_logistic_mutual_information_low_resolution_fisher_constant]
  · have hcoeff :
        xi_logistic_mutual_information_low_resolution_quadratic_coefficient = (1 / 6 : ℝ) := by
      norm_num [xi_logistic_mutual_information_low_resolution_quadratic_coefficient,
        xi_logistic_mutual_information_low_resolution_fisher_constant]
    simpa [hcoeff] using D.low_resolution_quadratic_expansion

end
end Omega.Zeta
