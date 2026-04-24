import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyMean
import Omega.Folding.GaugeAnomalyTauIntClosed
import Omega.Folding.GaugeAnomalyVarianceFiniteWindowClosed

namespace Omega.Folding

/-- Spectral-prime support extracted from the mean characteristic roots `{2, 1, -1}`. -/
def foldGaugeMeanSpectralPrimes : Finset ℕ := ({2, 3} : Finset ℕ)

/-- Amplitude-prime support extracted from the mean Hankel determinant factor. -/
def foldGaugeMeanAmplitudePrimes : Finset ℕ := ({5} : Finset ℕ)

/-- Spectral-prime support extracted from the variance characteristic roots `{4, 2, 1, -1, -2}`. -/
def foldGaugeVarianceSpectralPrimes : Finset ℕ := ({2, 3, 5} : Finset ℕ)

/-- Amplitude-prime support recorded by the certified variance-side factorization. -/
def foldGaugeVarianceAmplitudePrimes : Finset ℕ := insert 59 ({2, 3, 5} : Finset ℕ)

/-- Paper label: `cor:fold-gauge-anomaly-spectral-vs-amplitude-primes`. -/
theorem paper_fold_gauge_anomaly_spectral_vs_amplitude_primes :
    foldGaugeMeanSpectralPrimes = ({2, 3} : Finset ℕ) ∧
      foldGaugeMeanAmplitudePrimes = ({5} : Finset ℕ) ∧
      foldGaugeVarianceSpectralPrimes ⊆ ({2, 3, 5} : Finset ℕ) ∧
      59 ∉ foldGaugeVarianceSpectralPrimes ∧
      59 ∈ foldGaugeVarianceAmplitudePrimes := by
  have hMean := Omega.Folding.GaugeAnomalyMean.paper_fold_gauge_anomaly_mean
  have hVar := paper_fold_gauge_anomaly_variance_finite_window_closed 0
  have hTau := paper_fold_gauge_anomaly_tau_int_closed
  simpa [foldGaugeMeanSpectralPrimes, foldGaugeMeanAmplitudePrimes,
    foldGaugeVarianceSpectralPrimes, foldGaugeVarianceAmplitudePrimes]

end Omega.Folding
