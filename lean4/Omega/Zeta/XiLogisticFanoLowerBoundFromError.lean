import Mathlib.Tactic
import Omega.POM.FoldInversionZeroRateStrongConverse
import Omega.Zeta.XiLogisticDivergenceDictionary

namespace Omega.Zeta

/-- Concrete logistic/Fano data: the multiclass conditional entropy is bounded by the Fano cap
evaluated at the explicit logistic Bayes error, and the usual entropy decomposition relates it to
the mutual information. -/
structure xi_logistic_fano_lower_bound_from_error_data where
  classCount : Nat
  shift : ℝ
  conditionalEntropy : ℝ
  mutualInformation : ℝ
  classCount_two_le : 2 ≤ classCount
  conditionalEntropy_le_fano :
    conditionalEntropy ≤
      Omega.POM.pomBinaryEntropy (xiLogisticBayesError shift) +
        xiLogisticBayesError shift * Real.log ((classCount - 1 : Nat) : ℝ)
  information_plus_conditional :
    Real.log (classCount : ℝ) ≤ mutualInformation + conditionalEntropy

/-- The Fano penalty obtained from the logistic Bayes error. -/
noncomputable def xi_logistic_fano_lower_bound_from_error_penalty
    (D : xi_logistic_fano_lower_bound_from_error_data) : ℝ :=
  Omega.POM.pomBinaryEntropy (xiLogisticBayesError D.shift) +
    xiLogisticBayesError D.shift * Real.log ((D.classCount - 1 : Nat) : ℝ)

/-- The logistic Bayes error has its closed form, and Fano gives the corresponding lower bound on
mutual information. -/
def xi_logistic_fano_lower_bound_from_error_statement
    (D : xi_logistic_fano_lower_bound_from_error_data) : Prop :=
  xiLogisticBayesError D.shift = 1 / (1 + Real.exp (|D.shift| / 2)) ∧
    Real.log (D.classCount : ℝ) - xi_logistic_fano_lower_bound_from_error_penalty D ≤
      D.mutualInformation

/-- Paper label: `cor:xi-logistic-fano-lower-bound-from-error`. -/
theorem paper_xi_logistic_fano_lower_bound_from_error
    (D : xi_logistic_fano_lower_bound_from_error_data) :
    xi_logistic_fano_lower_bound_from_error_statement D := by
  refine ⟨?_, ?_⟩
  · exact (paper_xi_logistic_divergence_dictionary D.shift).2.1
  · have hcond :
        D.conditionalEntropy ≤ xi_logistic_fano_lower_bound_from_error_penalty D := by
      simpa [xi_logistic_fano_lower_bound_from_error_penalty] using D.conditionalEntropy_le_fano
    linarith [D.information_plus_conditional, hcond]

end Omega.Zeta
