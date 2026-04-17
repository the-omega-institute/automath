import Mathlib.Tactic
import Omega.Folding.BayesKinkGeometry
import Omega.Folding.BernoulliPBitpairLaw
import Omega.Folding.GaugeAnomalyMean

namespace Omega.Folding

/-- A rational checkpoint matching the already verified `4/9` gauge-anomaly core. -/
theorem fold_gauge_anomaly_density_core_checkpoint : ((1 : ℚ) / 9 + 1 / 3) = 4 / 9 := by
  norm_num

/-- Uniform Bernoulli gauge-anomaly density:
    the midpoint mismatch law sums to `4/9`, matching the existing checkpoint. -/
theorem paper_fold_gauge_anomaly_density :
    Omega.Folding.gStar (1 / 2 : Rat) = 4 / 9 ∧
      (((7 : Rat) / 18) + 1 / 9 + 1 / 3 + 1 / 6 = 1) ∧
      (1 / 9 + 1 / 3 = Omega.Folding.gStar (1 / 2 : Rat)) := by
  have hlaw :=
    Omega.Folding.paper_fold_gauge_anomaly_bernoulli_p_bitpair_law (p := (1 / 2 : Real))
      (by norm_num) (by norm_num)
  have hsum : ((1 - (1 / 2 : Real) - (1 / 2 : Real)^2 + 2 * (1 / 2 : Real)^3
      - (1 / 2 : Real)^4) / (1 + (1 / 2 : Real)^3)) +
      (((1 / 2 : Real)^2 * (1 - (1 / 2 : Real))) / (1 + (1 / 2 : Real)^3)) +
      (((1 / 2 : Real)^2 * (2 - (1 / 2 : Real))) / (1 + (1 / 2 : Real)^3)) +
      (((1 / 2 : Real) * ((1 / 2 : Real)^3 + (1 - (1 / 2 : Real))^2)) /
        (1 + (1 / 2 : Real)^3)) = 1 := hlaw.1
  have hmismatch :
      (((1 / 2 : Real)^2 * (1 - (1 / 2 : Real))) / (1 + (1 / 2 : Real)^3)) +
        (((1 / 2 : Real)^2 * (2 - (1 / 2 : Real))) / (1 + (1 / 2 : Real)^3)) = 4 / 9 := by
    have hmismatch' := hlaw.2.2
    norm_num at hmismatch' ⊢
  norm_num at hsum
  norm_num at hmismatch
  refine ⟨paper_fold_gauge_anomaly_density_49, ?_, ?_⟩
  · norm_num
  · rw [fold_gauge_anomaly_density_core_checkpoint, paper_fold_gauge_anomaly_density_49]

end Omega.Folding
