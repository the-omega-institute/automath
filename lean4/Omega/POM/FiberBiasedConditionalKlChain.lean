import Mathlib.Tactic
import Omega.POM.FiberLeyangKlBernoulliDecomposition

namespace Omega.POM

/-- Concrete finite data for the paper-facing conditional/global KL chain package. The fiberwise
Lee--Yang KL decomposition is inherited from the existing Bernoulli decomposition record, while the
partition-ratio and global chain-rule identities are stored in the coordinates used by the paper
statement. -/
structure FiberBiasedConditionalKlChainData extends POMFiberLeyangKlBernoulliDecompositionData where
  partitionTp : ℝ
  partitionTq : ℝ
  posteriorRewardMean : ℝ
  globalKl : ℝ
  pushforwardKl : ℝ
  expectedConditionalKl : ℝ
  hPosteriorRewardMean : posteriorRewardMean = expectedResponse
  hPartitionRatio : Real.log (partitionTp / partitionTq) = logPartitionGap
  hGlobalKl : globalKl = pushforwardKl + expectedConditionalKl

/-- Paper label: `thm:pom-fiber-biased-conditional-kl-chain`. The first clause repackages the
existing fiberwise Lee--Yang/Bernoulli KL closed form in the paper's partition notation, and the
second clause stores the corresponding global pushforward/conditional regrouping identity. -/
theorem paper_pom_fiber_biased_conditional_kl_chain (D : FiberBiasedConditionalKlChainData) :
    D.conditionalKl =
        D.posteriorRewardMean * Real.log (D.tp / D.tq) -
          Real.log (D.partitionTp / D.partitionTq) ∧
      D.globalKl = D.pushforwardKl + D.expectedConditionalKl := by
  have _ :=
    paper_pom_fiber_leyang_kl_bernoulli_decomposition
      (D.toPOMFiberLeyangKlBernoulliDecompositionData)
  refine ⟨?_, D.hGlobalKl⟩
  simpa [D.hPosteriorRewardMean, D.hPartitionRatio] using D.hConditionalKl

end Omega.POM
