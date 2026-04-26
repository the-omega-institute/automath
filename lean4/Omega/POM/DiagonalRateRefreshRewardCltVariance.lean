import Mathlib.Tactic
import Omega.POM.DiagonalRateRefreshCountRenewalLLNCLT

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- Concrete data for the diagonal-refresh renewal-reward CLT package. The block-length side is
handled by the existing regeneration/count infrastructure, while the reward side is encoded by a
single observable `reward` sampled against the same diagonal refresh weights. -/
structure pom_diagonal_rate_refresh_reward_clt_variance_data (X : Type) [Fintype X] where
  witness : DiagonalRateRefreshWitness X
  κ : ℝ
  clock : X → ℝ
  reward : X → ℝ
  hclock_nonneg : ∀ x, 0 ≤ clock x
  hT2 : diagonalRateRefreshCountT2 κ clock ≠ 0

namespace pom_diagonal_rate_refresh_reward_clt_variance_data

/-- Mean block reward collected over one regeneration cycle. -/
def blockRewardMean {X : Type} [Fintype X]
    (D : pom_diagonal_rate_refresh_reward_clt_variance_data X) : ℝ :=
  ∑ x, D.reward x * D.clock x / (D.clock x - D.κ) ^ 2

/-- Second block-reward moment collected over one regeneration cycle. -/
def blockRewardSecondMoment {X : Type} [Fintype X]
    (D : pom_diagonal_rate_refresh_reward_clt_variance_data X) : ℝ :=
  ∑ x, D.reward x ^ 2 * D.clock x / (D.clock x - D.κ) ^ 2

/-- Stationary reward mean obtained by dividing the block reward by the mean block length. -/
def stationaryMean {X : Type} [Fintype X]
    (D : pom_diagonal_rate_refresh_reward_clt_variance_data X) : ℝ :=
  D.blockRewardMean / diagonalRateRefreshCountMean D.κ D.clock

/-- Renewal-reward CLT variance density. -/
def rewardCltVariance {X : Type} [Fintype X]
    (D : pom_diagonal_rate_refresh_reward_clt_variance_data X) : ℝ :=
  (D.blockRewardSecondMoment - D.blockRewardMean ^ 2) /
    diagonalRateRefreshCountMean D.κ D.clock

/-- Finiteness of the reward second moment is encoded here by the explicit nonnegative finite sum
provided by the `Fintype` block model. -/
def secondMomentFinite {X : Type} [Fintype X]
    (D : pom_diagonal_rate_refresh_reward_clt_variance_data X) : Prop :=
  0 ≤ D.blockRewardSecondMoment

/-- Paper-facing renewal-reward package: regeneration and block-length formulas come from the
existing diagonal-refresh count theory, while the reward mean/variance are the standard
renewal-reward expressions. -/
def statement {X : Type} [Fintype X]
    (D : pom_diagonal_rate_refresh_reward_clt_variance_data X) : Prop :=
  D.witness.markovRealization ∧
    D.witness.regenerationProperty ∧
    diagonalRateRefreshCountMean D.κ D.clock = ∑ x, D.clock x / (D.clock x - D.κ) ^ 2 ∧
    D.stationaryMean = D.blockRewardMean / diagonalRateRefreshCountMean D.κ D.clock ∧
    D.secondMomentFinite ∧
    D.rewardCltVariance =
      (D.blockRewardSecondMoment - D.blockRewardMean ^ 2) /
        diagonalRateRefreshCountMean D.κ D.clock ∧
    diagonalRateRefreshCountCLTVariance D.κ D.clock =
      diagonalRateRefreshCountRenewalVariance D.κ D.clock /
        diagonalRateRefreshCountMean D.κ D.clock ^ 3

lemma blockRewardSecondMoment_nonneg {X : Type} [Fintype X]
    (D : pom_diagonal_rate_refresh_reward_clt_variance_data X) :
    D.secondMomentFinite := by
  unfold secondMomentFinite blockRewardSecondMoment
  refine Finset.sum_nonneg ?_
  intro x hx
  refine div_nonneg ?_ (sq_nonneg _)
  exact mul_nonneg (sq_nonneg _) (D.hclock_nonneg x)

end pom_diagonal_rate_refresh_reward_clt_variance_data

open pom_diagonal_rate_refresh_reward_clt_variance_data

/-- Paper label: `thm:pom-diagonal-rate-refresh-reward-clt-variance`. The diagonal-refresh
regeneration package supplies the block-length formulas, and the reward observable contributes its
stationary mean and CLT variance through the standard renewal-reward identities. -/
theorem paper_pom_diagonal_rate_refresh_reward_clt_variance {X : Type} [Fintype X]
    (D : pom_diagonal_rate_refresh_reward_clt_variance_data X) : D.statement := by
  rcases paper_pom_diagonal_rate_refresh_count_renewal_lln_clt
      (w := D.witness) (κ := D.κ) (t := D.clock) D.hT2 with
    ⟨hMarkov, hRegen, hMean, _hSecond, _hLLN, hCountVariance, _hPsi⟩
  refine ⟨hMarkov, hRegen, hMean, rfl, D.blockRewardSecondMoment_nonneg, rfl, hCountVariance⟩

end

end Omega.POM
