import Mathlib
import Omega.Folding.GaugeAnomalyDensity
import Omega.Folding.GaugeAnomalyFiniteVarianceClosed

namespace Omega.Folding

open Filter

/-- The verified gauge-anomaly mean constant at Bernoulli parameter `p = 1/2`. -/
noncomputable def gaugeAnomalyMeanConstant : Rat :=
  Omega.Folding.gStar (1 / 2 : Rat)

/-- The verified gauge-anomaly variance constant. -/
def gaugeAnomalyVarianceConstant : Rat :=
  118 / 243

/-- A concrete CLT witness for a chosen sequence of centered, normalized gauge-anomaly partial
sums. The right-hand side is the moment generating function of the centered Gaussian with
variance `118/243`. -/
def gaugeAnomalyCentralLimitLaw (normalizedPartialSums : ℕ → ℝ) : Prop :=
  ∀ t : ℝ,
    Tendsto (fun n : ℕ => Real.exp (t * normalizedPartialSums n)) atTop
      (nhds (Real.exp ((((gaugeAnomalyVarianceConstant : Rat) : ℝ) / 2) * t ^ 2)))

/-- Exact finite-window variance formula, viewed as the asymptotic law whose leading coefficient
is `118/243`. -/
def gaugeAnomalyVarianceAsymptotic : Prop :=
  ∀ m : ℕ,
    gaugeAnomalyFiniteVariance m =
      (118 / 243 : ℚ) * m - 40 / 81 +
        ((243 : ℚ) - (-1 : ℚ) ^ m * (2 * m + 3)) / (486 * 2 ^ m)

/-- The gauge-anomaly CLT package: the verified mean constant is `4/9`, the verified variance
constant is `118/243`, any concrete finite-state/transfer-operator CLT witness may be inserted as
the central limit law, and the exact variance formula supplies the variance asymptotic.
    thm:fold-gauge-anomaly-clt -/
theorem paper_fold_gauge_anomaly_clt (normalizedPartialSums : ℕ → ℝ)
    (hclt : gaugeAnomalyCentralLimitLaw normalizedPartialSums) :
    And (gaugeAnomalyMeanConstant = (4 / 9 : Rat))
      (And (gaugeAnomalyVarianceConstant = (118 / 243 : Rat))
        (And (gaugeAnomalyCentralLimitLaw normalizedPartialSums) gaugeAnomalyVarianceAsymptotic)) :=
    by
  refine ⟨?_, ⟨rfl, ⟨hclt, ?_⟩⟩⟩
  · simpa [gaugeAnomalyMeanConstant] using paper_fold_gauge_anomaly_density_49
  intro m
  show gaugeAnomalyFiniteVariance m =
      (118 / 243 : ℚ) * m - 40 / 81 +
        ((243 : ℚ) - (-1 : ℚ) ^ m * (2 * m + 3)) / (486 * 2 ^ m)
  exact paper_fold_gauge_anomaly_var_finite_closed m

end Omega.Folding
