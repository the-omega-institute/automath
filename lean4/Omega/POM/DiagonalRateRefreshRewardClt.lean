import Mathlib.Tactic
import Omega.POM.DiagonalRateRefreshRewardCltVariance

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- Concrete data for the diagonal-refresh renewal-reward CLT with the centered observable
`f - μ_f`. -/
structure pom_diagonal_rate_refresh_reward_clt_data (X : Type) [Fintype X] where
  witness : DiagonalRateRefreshWitness X
  κ : ℝ
  clock : X → ℝ
  observable : X → ℝ
  hclock_nonneg : ∀ x, 0 ≤ clock x
  hT2 : diagonalRateRefreshCountT2 κ clock ≠ 0

namespace pom_diagonal_rate_refresh_reward_clt_data

/-- Block reward accumulated over one regeneration cycle. -/
def pom_diagonal_rate_refresh_reward_clt_observableMoment {X : Type} [Fintype X]
    (D : pom_diagonal_rate_refresh_reward_clt_data X) : ℝ :=
  ∑ x, D.observable x * D.clock x / (D.clock x - D.κ) ^ 2

/-- Stationary observable mean obtained by dividing the block reward by the mean block length. -/
def pom_diagonal_rate_refresh_reward_clt_stationaryMean {X : Type} [Fintype X]
    (D : pom_diagonal_rate_refresh_reward_clt_data X) : ℝ :=
  D.pom_diagonal_rate_refresh_reward_clt_observableMoment / diagonalRateRefreshCountMean D.κ D.clock

/-- Centered observable `f - μ_f`. -/
def pom_diagonal_rate_refresh_reward_clt_centeredObservable {X : Type} [Fintype X]
    (D : pom_diagonal_rate_refresh_reward_clt_data X) (x : X) : ℝ :=
  D.observable x - D.pom_diagonal_rate_refresh_reward_clt_stationaryMean

/-- Mean centered block reward. -/
def pom_diagonal_rate_refresh_reward_clt_centeredBlockMean {X : Type} [Fintype X]
    (D : pom_diagonal_rate_refresh_reward_clt_data X) : ℝ :=
  D.pom_diagonal_rate_refresh_reward_clt_observableMoment -
    D.pom_diagonal_rate_refresh_reward_clt_stationaryMean *
      diagonalRateRefreshCountMean D.κ D.clock

/-- Second moment of the centered block reward. -/
def pom_diagonal_rate_refresh_reward_clt_centeredBlockSecondMoment {X : Type} [Fintype X]
    (D : pom_diagonal_rate_refresh_reward_clt_data X) : ℝ :=
  ∑ x,
    (D.pom_diagonal_rate_refresh_reward_clt_centeredObservable x) ^ 2 * D.clock x /
      (D.clock x - D.κ) ^ 2

/-- Renewal-reward CLT variance density for the centered observable. -/
def pom_diagonal_rate_refresh_reward_clt_varianceDensity {X : Type} [Fintype X]
    (D : pom_diagonal_rate_refresh_reward_clt_data X) : ℝ :=
  (D.pom_diagonal_rate_refresh_reward_clt_centeredBlockSecondMoment -
      D.pom_diagonal_rate_refresh_reward_clt_centeredBlockMean ^ 2) /
    diagonalRateRefreshCountMean D.κ D.clock

/-- The centered observable packaged for the nearby renewal-reward variance wrapper. -/
def pom_diagonal_rate_refresh_reward_clt_varianceData {X : Type} [Fintype X]
    (D : pom_diagonal_rate_refresh_reward_clt_data X) :
    pom_diagonal_rate_refresh_reward_clt_variance_data X where
  witness := D.witness
  κ := D.κ
  clock := D.clock
  reward := D.pom_diagonal_rate_refresh_reward_clt_centeredObservable
  hclock_nonneg := D.hclock_nonneg
  hT2 := D.hT2

/-- Paper-facing package for the centered additive-functional CLT. -/
def statement {X : Type} [Fintype X] (D : pom_diagonal_rate_refresh_reward_clt_data X) : Prop :=
  D.witness.markovRealization ∧
    D.witness.regenerationProperty ∧
    D.pom_diagonal_rate_refresh_reward_clt_stationaryMean =
      D.pom_diagonal_rate_refresh_reward_clt_observableMoment /
        diagonalRateRefreshCountMean D.κ D.clock ∧
    D.pom_diagonal_rate_refresh_reward_clt_centeredBlockMean = 0 ∧
    0 ≤ D.pom_diagonal_rate_refresh_reward_clt_centeredBlockSecondMoment ∧
    D.pom_diagonal_rate_refresh_reward_clt_varianceDensity =
      (D.pom_diagonal_rate_refresh_reward_clt_centeredBlockSecondMoment -
          D.pom_diagonal_rate_refresh_reward_clt_centeredBlockMean ^ 2) /
        diagonalRateRefreshCountMean D.κ D.clock ∧
    diagonalRateRefreshCountCLTVariance D.κ D.clock =
      diagonalRateRefreshCountRenewalVariance D.κ D.clock /
        diagonalRateRefreshCountMean D.κ D.clock ^ 3

lemma pom_diagonal_rate_refresh_reward_clt_centeredBlockMean_zero {X : Type} [Fintype X]
    (D : pom_diagonal_rate_refresh_reward_clt_data X) :
    D.pom_diagonal_rate_refresh_reward_clt_centeredBlockMean = 0 := by
  have hMean_ne : diagonalRateRefreshCountMean D.κ D.clock ≠ 0 := by
    simpa [diagonalRateRefreshCountMean] using D.hT2
  unfold pom_diagonal_rate_refresh_reward_clt_centeredBlockMean
    pom_diagonal_rate_refresh_reward_clt_stationaryMean
  field_simp [hMean_ne]
  ring

lemma pom_diagonal_rate_refresh_reward_clt_centeredBlockSecondMoment_nonneg {X : Type}
    [Fintype X] (D : pom_diagonal_rate_refresh_reward_clt_data X) :
    0 ≤ D.pom_diagonal_rate_refresh_reward_clt_centeredBlockSecondMoment := by
  have hsecond :=
    (D.pom_diagonal_rate_refresh_reward_clt_varianceData).blockRewardSecondMoment_nonneg
  simpa [pom_diagonal_rate_refresh_reward_clt_varianceData,
    pom_diagonal_rate_refresh_reward_clt_centeredBlockSecondMoment,
    pom_diagonal_rate_refresh_reward_clt_centeredObservable] using hsecond

end pom_diagonal_rate_refresh_reward_clt_data

open pom_diagonal_rate_refresh_reward_clt_data

/-- Paper label: `thm:pom-diagonal-rate-refresh-reward-clt`. The diagonal-refresh regeneration
package yields the centered block reward `H (f(Y) - μ_f)`, whose mean vanishes by construction and
whose finite second moment is the explicit nonnegative finite sum appearing in the renewal-reward
variance formula. -/
theorem paper_pom_diagonal_rate_refresh_reward_clt {X : Type} [Fintype X]
    (D : pom_diagonal_rate_refresh_reward_clt_data X) : D.statement := by
  rcases paper_pom_diagonal_rate_refresh_reward_clt_variance
      (D := D.pom_diagonal_rate_refresh_reward_clt_varianceData) with
    ⟨hMarkov, hRegen, _hMean, _hStationaryMean, hSecondMoment, hVariance, hCountVariance⟩
  refine ⟨hMarkov, hRegen, rfl, D.pom_diagonal_rate_refresh_reward_clt_centeredBlockMean_zero, ?_,
    ?_, hCountVariance⟩
  · simpa [pom_diagonal_rate_refresh_reward_clt_varianceData,
      pom_diagonal_rate_refresh_reward_clt_centeredBlockSecondMoment,
      pom_diagonal_rate_refresh_reward_clt_centeredObservable] using hSecondMoment
  · simpa [pom_diagonal_rate_refresh_reward_clt_varianceDensity,
      pom_diagonal_rate_refresh_reward_clt_varianceData,
      pom_diagonal_rate_refresh_reward_clt_centeredBlockSecondMoment,
      pom_diagonal_rate_refresh_reward_clt_centeredBlockMean,
      pom_diagonal_rate_refresh_reward_clt_centeredObservable] using hVariance

end

end Omega.POM
