import Mathlib.Tactic
import Omega.Conclusion.CriticalKernelTensorPdetHalfentropyParam
import Omega.Conclusion.CriticalKernelSingleEigenpairRecoversDistribution

namespace Omega.Conclusion

open scoped BigOperators

/-- Certificate for the endpoint half-entropy pdet tower rigidity package.  It combines the
already formalized tensor pdet half-entropy formula, the single-eigenpair reconstruction datum,
and the uniform-minimizer hypotheses for the critical kernel. -/
structure conclusion_endpoint_halfentropy_pdet_tower_rigidity_certificate where
  tensorData : conclusion_critical_kernel_tensor_pdet_halfentropy_param_data
  n : ℕ
  hn : 2 ≤ n
  w : Fin n → ℝ
  w_pos : ∀ i, 0 < w i
  w_sum : (∑ i, w i) = 1
  t : Fin n → ℝ
  v : Fin n → ℝ
  lam : ℝ
  sigma : ℝ
  t_injective : Function.Injective t
  eigenvector_nonzero : ∃ x, v x ≠ 0
  sigma_sum : sigma = ∑ x, v x
  eigenpair_eq : ∀ x, (t x - lam) * v x = sigma
  recovered_distribution :
    ∀ x, w x = (1 / (t x)^2) / (∑ u, 1 / (t u)^2)

namespace conclusion_endpoint_halfentropy_pdet_tower_rigidity_certificate

/-- The tower pdet expression is the previously proved half-entropy single-parameter form. -/
def towerDependsOnlyOnHalfEntropy
    (C : conclusion_endpoint_halfentropy_pdet_tower_rigidity_certificate) : Prop :=
  C.tensorData.tensor_pdet_halfentropy_param

/-- A single critical eigenpair recovers the normalized endpoint distribution. -/
def singleLayerRecoversHalfEntropy
    (C : conclusion_endpoint_halfentropy_pdet_tower_rigidity_certificate) : Prop :=
  C.sigma ≠ 0 ∧
    (∀ x, C.v x ≠ 0 ∧ C.t x = C.lam + C.sigma / C.v x) ∧
      ∀ x,
        C.w x =
          (1 / (C.lam + C.sigma / C.v x)^2) /
            (∑ u, 1 / (C.lam + C.sigma / C.v u)^2)

/-- The uniform critical-kernel benchmark is the global lower bound for the pdet functional. -/
def uniformUniqueMinimizer
    (C : conclusion_endpoint_halfentropy_pdet_tower_rigidity_certificate) : Prop :=
  ((C.n : ℝ) / (C.n - 1)) ^ (C.n - 1) ≤ criticalKernelPdet C.w

end conclusion_endpoint_halfentropy_pdet_tower_rigidity_certificate

/-- Paper label: `thm:conclusion-endpoint-halfentropy-pdet-tower-rigidity`. -/
theorem paper_conclusion_endpoint_halfentropy_pdet_tower_rigidity
    (C : conclusion_endpoint_halfentropy_pdet_tower_rigidity_certificate) :
    C.towerDependsOnlyOnHalfEntropy ∧ C.singleLayerRecoversHalfEntropy ∧
      C.uniformUniqueMinimizer := by
  refine ⟨?_, ?_, ?_⟩
  · exact paper_conclusion_critical_kernel_tensor_pdet_halfentropy_param C.tensorData
  · exact
      paper_conclusion_critical_kernel_single_eigenpair_recovers_distribution C.t C.v C.w
        C.lam C.sigma C.t_injective C.eigenvector_nonzero C.sigma_sum C.eigenpair_eq
        C.recovered_distribution
  · exact paper_conclusion_critical_kernel_pdet_uniform_minimizer C.n C.hn C.w C.w_pos C.w_sum

end Omega.Conclusion
