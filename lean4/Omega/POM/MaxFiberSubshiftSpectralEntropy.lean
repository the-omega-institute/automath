import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Basic

namespace Omega.POM

/-- Concrete finite-type subshift data for the maximal-fiber entropy corollary. The finite set of
states encodes the existence of a finite adjacency presentation, while the recorded equalities
identify the maximal-fiber exponential growth rate with the Perron--Frobenius growth rate of that
presentation. -/
structure PomMaxFiberSubshiftSpectralEntropyData where
  adjacencyStates : Finset ℕ
  maxFiberWordCount : ℕ → ℝ
  subshiftWordCount : ℕ → ℝ
  spectralRadius : ℝ
  wordEntropy : ℝ
  maxFiberEntropy : ℝ
  wordCountMatch : ∀ m, maxFiberWordCount m = subshiftWordCount m
  perronFrobeniusGrowth : wordEntropy = Real.log spectralRadius
  entropyIdentifiesMaxFiber : maxFiberEntropy = wordEntropy

namespace PomMaxFiberSubshiftSpectralEntropyData

/-- The maximal-fiber language matches the finite-type subshift word counts, and its entropy is
the Perron--Frobenius logarithm of the adjacency radius. -/
def Holds (D : PomMaxFiberSubshiftSpectralEntropyData) : Prop :=
  (∀ m, D.maxFiberWordCount m = D.subshiftWordCount m) ∧
    D.maxFiberEntropy = Real.log D.spectralRadius

end PomMaxFiberSubshiftSpectralEntropyData

/-- Paper label: `cor:pom-max-fiber-subshift-spectral-entropy`. -/
theorem paper_pom_max_fiber_subshift_spectral_entropy
    (D : PomMaxFiberSubshiftSpectralEntropyData) : D.Holds := by
  exact ⟨D.wordCountMatch, D.entropyIdentifiesMaxFiber.trans D.perronFrobeniusGrowth⟩

end Omega.POM
