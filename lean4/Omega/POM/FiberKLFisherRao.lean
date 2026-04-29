import Mathlib.Tactic
import Omega.POM.FiberBiasedConditionalKlChain

namespace Omega.POM

/-- Concrete paper-facing data for the conditional KL variance-potential/Fisher--Rao package.
The fields are the finite-dimensional quantities appearing in the paper proof: the conditional
KL value, the mean-response integral, the variance-potential integral, the Fisher metric, and the
quadratic local term in natural parameter coordinates. -/
structure pom_fiber_kl_variance_potential_fisher_rao_data where
  conditionalKl : ℝ
  meanResponseIntegral : ℝ
  variancePotentialIntegral : ℝ
  fisherRaoMetric : ℝ
  naturalStep : ℝ
  localQuadraticTerm : ℝ
  klChain : conditionalKl = meanResponseIntegral
  derivativeVarianceRelation : meanResponseIntegral = variancePotentialIntegral
  fisherRaoVariance : fisherRaoMetric = variancePotentialIntegral
  localVarianceExpansion :
    localQuadraticTerm = (1 / 2) * variancePotentialIntegral * naturalStep ^ 2

namespace pom_fiber_kl_variance_potential_fisher_rao_data

/-- The conditional KL is represented by both the mean-response and variance-potential
integrals, and the local second-order coefficient is the Fisher--Rao metric. -/
def kl_variance_potential (D : pom_fiber_kl_variance_potential_fisher_rao_data) : Prop :=
  D.conditionalKl = D.meanResponseIntegral ∧
    D.conditionalKl = D.variancePotentialIntegral ∧
    D.localQuadraticTerm = (1 / 2) * D.fisherRaoMetric * D.naturalStep ^ 2

end pom_fiber_kl_variance_potential_fisher_rao_data

/-- Paper label: `thm:pom-fiber-kl-variance-potential-fisher-rao`. The conditional KL chain and
the derivative/variance identity identify the KL potential with the variance potential, while the
same variance is the local Fisher--Rao quadratic coefficient. -/
theorem paper_pom_fiber_kl_variance_potential_fisher_rao
    (D : pom_fiber_kl_variance_potential_fisher_rao_data) :
    D.kl_variance_potential := by
  refine ⟨D.klChain, ?_, ?_⟩
  · exact D.klChain.trans D.derivativeVarianceRelation
  · calc
      D.localQuadraticTerm =
          (1 / 2) * D.variancePotentialIntegral * D.naturalStep ^ 2 :=
        D.localVarianceExpansion
      _ = (1 / 2) * D.fisherRaoMetric * D.naturalStep ^ 2 := by
        rw [D.fisherRaoVariance]

end Omega.POM
