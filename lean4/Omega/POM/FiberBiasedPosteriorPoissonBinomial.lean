import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.POM.FiberBiasedBernoulliPushforwardHardcore
import Omega.POM.FiberRewritePoissonBinomial

namespace Omega.POM

open scoped BigOperators
open FiberBiasedBernoulliPushforwardHardcoreData

noncomputable section

/-- Concrete fiberwise Lee--Yang data for turning the posterior PGF into a Poisson-binomial
factorization. The root parameters are positive, and the weighted fiber polynomial factors after
normalization by the partition function. -/
structure FiberBiasedPosteriorPoissonBinomialData where
  base : FiberBiasedBernoulliPushforwardHardcoreData
  fiber : base.X
  rootCount : ℕ
  alpha : Fin rootCount → ℝ
  halpha : ∀ j, 0 < alpha j
  hWeightedRootFactorization :
    ∀ t : ℝ,
      ∑ ω : {ω // base.fold ω = fiber}, (base.activity ^ base.reward ω.1) * t ^ base.reward ω.1 =
        base.partitionFunction fiber * ∏ j : Fin rootCount, ((alpha j + t) / (alpha j + 1))

namespace FiberBiasedPosteriorPoissonBinomialData

/-- The posterior PGF of the fiber reward under the biased Bernoulli posterior. -/
def posteriorPgf (D : FiberBiasedPosteriorPoissonBinomialData) (t : ℝ) : ℝ :=
  ∑ ω : {ω // D.base.fold ω = D.fiber}, D.base.posteriorMass D.fiber ω * t ^ D.base.reward ω.1

/-- The mean read off from the Lee--Yang/Bernoulli parameters. -/
def posteriorMean (D : FiberBiasedPosteriorPoissonBinomialData) : ℝ :=
  ∑ j : Fin D.rootCount, 1 / (1 + D.alpha j)

/-- The variance read off from the Lee--Yang/Bernoulli parameters. -/
def posteriorVariance (D : FiberBiasedPosteriorPoissonBinomialData) : ℝ :=
  ∑ j : Fin D.rootCount, D.alpha j / (1 + D.alpha j) ^ 2

/-- The normalized posterior PGF factors as a Poisson-binomial PGF, with the corresponding mean
and variance formulas. -/
def poissonBinomialDecomposition (D : FiberBiasedPosteriorPoissonBinomialData) : Prop :=
  ∃ p : Fin D.rootCount → ℝ,
    (∀ j, 0 < p j ∧ p j < 1) ∧
      (∀ t : ℝ, D.posteriorPgf t = ∏ j : Fin D.rootCount, (1 - p j + p j * t)) ∧
      D.posteriorMean = ∑ j : Fin D.rootCount, p j ∧
      D.posteriorVariance = ∑ j : Fin D.rootCount, p j * (1 - p j)

lemma posteriorPgf_eq_normalizedProduct (D : FiberBiasedPosteriorPoissonBinomialData) (t : ℝ) :
    D.posteriorPgf t = ∏ j : Fin D.rootCount, ((D.alpha j + t) / (D.alpha j + 1)) := by
  rcases paper_pom_fiber_biased_bernoulli_pushforward_hardcore D.base with ⟨_, hpost, _⟩
  have hpart_pos : 0 < D.base.partitionFunction D.fiber := D.base.partitionFunction_pos D.fiber
  have hpart_ne : D.base.partitionFunction D.fiber ≠ 0 := hpart_pos.ne'
  calc
    D.posteriorPgf t
        = ∑ ω : {ω // D.base.fold ω = D.fiber},
            (D.base.activity ^ D.base.reward ω.1 / D.base.partitionFunction D.fiber) *
              t ^ D.base.reward ω.1 := by
              unfold posteriorPgf
              refine Finset.sum_congr rfl ?_
              intro ω hω
              rw [hpost D.fiber ω]
    _ = ∑ ω : {ω // D.base.fold ω = D.fiber},
          ((D.base.activity ^ D.base.reward ω.1) * t ^ D.base.reward ω.1) /
            D.base.partitionFunction D.fiber := by
              refine Finset.sum_congr rfl ?_
              intro ω hω
              field_simp [hpart_ne]
    _ = (∑ ω : {ω // D.base.fold ω = D.fiber},
          (D.base.activity ^ D.base.reward ω.1) * t ^ D.base.reward ω.1) /
            D.base.partitionFunction D.fiber := by
              rw [Finset.sum_div]
    _ = (D.base.partitionFunction D.fiber *
          ∏ j : Fin D.rootCount, ((D.alpha j + t) / (D.alpha j + 1))) /
            D.base.partitionFunction D.fiber := by
              rw [D.hWeightedRootFactorization]
    _ = ∏ j : Fin D.rootCount, ((D.alpha j + t) / (D.alpha j + 1)) := by
          simpa [mul_comm] using
            (mul_div_cancel_left₀
              (∏ j : Fin D.rootCount, ((D.alpha j + t) / (D.alpha j + 1))) hpart_ne)

end FiberBiasedPosteriorPoissonBinomialData

open FiberBiasedPosteriorPoissonBinomialData

/-- The hard-core posterior theorem identifies the fiber PGF with the normalized fiber polynomial;
the Lee--Yang positive-root rewrite then packages this normalized PGF as a Poisson-binomial
product and reads off the corresponding mean and variance formulas.
    thm:pom-fiber-biased-posterior-poisson-binomial -/
theorem paper_pom_fiber_biased_posterior_poisson_binomial
    (D : FiberBiasedPosteriorPoissonBinomialData) : D.poissonBinomialDecomposition := by
  rcases paper_pom_fiber_rewrite_poisson_binomial D.rootCount D.alpha D.halpha with
    ⟨p, hp, hpgf, hmean, hvar⟩
  refine ⟨p, hp, ?_, ?_, ?_⟩
  · intro t
    rw [D.posteriorPgf_eq_normalizedProduct t, hpgf t]
  · simpa [FiberBiasedPosteriorPoissonBinomialData.posteriorMean] using hmean.symm
  · simpa [FiberBiasedPosteriorPoissonBinomialData.posteriorVariance] using hvar.symm

end

end Omega.POM
