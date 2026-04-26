import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete spectral data for a Hellinger Gram cluster. The power scale is the determinant
asymptotic scale `C * Δ^(κ(κ-1))`; the remaining fields record the finite-dimensional spectral
comparison between the smallest eigenvalue and the condition number. -/
structure xi_hellinger_gram_cluster_conditioning_exponent_data where
  kappa : ℕ
  separation : ℝ
  determinantConstant : ℝ
  minEigenvalue : ℝ
  referenceEigenvalue : ℝ
  conditionNumber : ℝ
  hconditionNumber_nonneg : 0 ≤ conditionNumber
  hminEigenvalue_power :
    minEigenvalue ≤ determinantConstant * separation ^ (kappa * (kappa - 1))
  hreference_lower : 1 ≤ referenceEigenvalue
  hreference_le_condition_min : referenceEigenvalue ≤ conditionNumber * minEigenvalue

namespace xi_hellinger_gram_cluster_conditioning_exponent_data

/-- The cluster determinant power scale `C Δ^(κ(κ-1))`. -/
def xi_hellinger_gram_cluster_conditioning_exponent_powerScale
    (D : xi_hellinger_gram_cluster_conditioning_exponent_data) : ℝ :=
  D.determinantConstant * D.separation ^ (D.kappa * (D.kappa - 1))

/-- The minimum Hellinger Gram eigenvalue is bounded above by the cluster power scale. -/
def minEigenvaluePowerUpperBound
    (D : xi_hellinger_gram_cluster_conditioning_exponent_data) : Prop :=
  D.minEigenvalue ≤ D.xi_hellinger_gram_cluster_conditioning_exponent_powerScale

/-- Equivalently, the condition number dominates the reciprocal power scale in product form. -/
def conditionNumberPowerBlowup
    (D : xi_hellinger_gram_cluster_conditioning_exponent_data) : Prop :=
  1 ≤ D.conditionNumber * D.xi_hellinger_gram_cluster_conditioning_exponent_powerScale

lemma xi_hellinger_gram_cluster_conditioning_exponent_conditionNumberPowerBlowup
    (D : xi_hellinger_gram_cluster_conditioning_exponent_data) :
    D.conditionNumberPowerBlowup := by
  calc
    1 ≤ D.referenceEigenvalue := D.hreference_lower
    _ ≤ D.conditionNumber * D.minEigenvalue := D.hreference_le_condition_min
    _ ≤ D.conditionNumber *
        D.xi_hellinger_gram_cluster_conditioning_exponent_powerScale := by
          exact mul_le_mul_of_nonneg_left D.hminEigenvalue_power D.hconditionNumber_nonneg

end xi_hellinger_gram_cluster_conditioning_exponent_data

/-- Paper label: `cor:xi-hellinger-gram-cluster-conditioning-exponent`. -/
theorem paper_xi_hellinger_gram_cluster_conditioning_exponent
    (D : xi_hellinger_gram_cluster_conditioning_exponent_data) :
    D.minEigenvaluePowerUpperBound ∧ D.conditionNumberPowerBlowup := by
  exact ⟨D.hminEigenvalue_power,
    D.xi_hellinger_gram_cluster_conditioning_exponent_conditionNumberPowerBlowup⟩

end Omega.Zeta
