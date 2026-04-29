import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Omega.Folding.GaugeAnomalySpectralVsAmplitudePrimes

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-secondorder-hankel-badprime-amplitude-splitting`. -/
theorem paper_conclusion_secondorder_hankel_badprime_amplitude_splitting :
    ({2, 3, 5, 59} : Finset ℕ) = ({2, 5} : Finset ℕ) ∪ ({3, 59} : Finset ℕ) ∧
      Disjoint ({2, 5} : Finset ℕ) ({3, 59} : Finset ℕ) ∧
      59 ∉ Omega.Folding.foldGaugeVarianceSpectralPrimes ∧
      59 ∈ Omega.Folding.foldGaugeVarianceAmplitudePrimes := by
  have hPrimeSplit := Omega.Folding.paper_fold_gauge_anomaly_spectral_vs_amplitude_primes
  constructor
  · ext p
    simp
    omega
  constructor
  · rw [Finset.disjoint_left]
    intro p hp hq
    simp at hp hq
    omega
  · exact ⟨hPrimeSplit.2.2.2.1, hPrimeSplit.2.2.2.2⟩

end Omega.Conclusion
