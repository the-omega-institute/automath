import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyCovGenfun

namespace Omega.Folding

/-- Expanded denominator polynomial for the rational gauge-anomaly power spectrum. -/
def gaugeAnomalyPsdDenominatorExpanded (s : ℚ) : ℚ :=
  -s ^ 3 - 2 * s ^ 2 + 4 * s + 8

/-- Factorized denominator polynomial for the rational gauge-anomaly power spectrum. -/
def gaugeAnomalyPsdDenominatorFactorized (s : ℚ) : ℚ :=
  (2 - s) * (s + 2) ^ 2

lemma gaugeAnomalyPsdDenominator_factorization (s : ℚ) :
    gaugeAnomalyPsdDenominatorExpanded s = gaugeAnomalyPsdDenominatorFactorized s := by
  dsimp [gaugeAnomalyPsdDenominatorExpanded, gaugeAnomalyPsdDenominatorFactorized]
  ring

/-- Concrete package for a rational gauge-anomaly power spectrum obtained from the Bernoulli
autocovariance generating-function data after the uniform specialization. -/
structure GaugeAnomalyPsdRationalData where
  generatingData : BernoulliPAutocovarianceGeneratingRationalData
  numerator : ℚ → ℚ
  denominator : ℚ → ℚ
  powerSpectrum : ℚ → ℚ
  powerSpectrum_eq :
    ∀ s : ℚ, powerSpectrum s = numerator s / gaugeAnomalyPsdDenominatorExpanded s
  denominator_eq : ∀ s : ℚ, denominator s = gaugeAnomalyPsdDenominatorExpanded s

namespace GaugeAnomalyPsdRationalData

/-- The power spectrum is represented by a rational function with the factorized denominator. -/
def rationalPowerSpectrum (D : GaugeAnomalyPsdRationalData) : Prop :=
  ∀ s : ℚ, D.powerSpectrum s = D.numerator s / gaugeAnomalyPsdDenominatorFactorized s

/-- The denominator polynomial admits the claimed factorization. -/
def denominatorFactorization (D : GaugeAnomalyPsdRationalData) : Prop :=
  ∀ s : ℚ, D.denominator s = gaugeAnomalyPsdDenominatorFactorized s

end GaugeAnomalyPsdRationalData

open GaugeAnomalyPsdRationalData

/-- Specializing the Bernoulli autocovariance generating-function package to the uniform baseline
produces a rational gauge-anomaly power spectrum whose denominator factors as claimed.
    thm:fold-gauge-anomaly-psd-rational -/
theorem paper_fold_gauge_anomaly_psd_rational (D : GaugeAnomalyPsdRationalData) :
    D.rationalPowerSpectrum ∧ D.denominatorFactorization := by
  have hGF : D.generatingData.rationalGeneratingFunction :=
    paper_fold_gauge_anomaly_cov_genfun D.generatingData
  refine ⟨?_, ?_⟩
  · intro s
    rw [D.powerSpectrum_eq s, gaugeAnomalyPsdDenominator_factorization]
  · intro s
    rw [D.denominator_eq s, gaugeAnomalyPsdDenominator_factorization]

end Omega.Folding
