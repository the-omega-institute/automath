import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete bookkeeping for the Dirac-versus-uniform holography separation estimate. -/
structure XiHolographyCoherenceSeparationData where
  alphabetSize : ℕ
  diracLogLikelihood : ℕ → ℝ
  uniformLogLikelihood : ℕ → ℝ
  conditionalComplexity : ℕ → ℝ
  overhead : ℝ
  alphabet_ge_two : 2 ≤ alphabetSize
  exactGap :
    ∀ n,
      diracLogLikelihood n - uniformLogLikelihood n = (n : ℝ) * Real.log (alphabetSize : ℝ)
  complexityBound :
    ∀ n, conditionalComplexity n ≤ overhead * Real.log (n + 1) + overhead

namespace XiHolographyCoherenceSeparationData

def linearEvidenceRate (D : XiHolographyCoherenceSeparationData) : Prop :=
  ∀ n,
    D.diracLogLikelihood n - D.uniformLogLikelihood n =
      (n : ℝ) * Real.log (D.alphabetSize : ℝ)

def zeroConditionalInformationRate (D : XiHolographyCoherenceSeparationData) : Prop :=
  ∃ C : ℝ, ∀ n, D.conditionalComplexity n ≤ C * Real.log (n + 1) + C

end XiHolographyCoherenceSeparationData

open XiHolographyCoherenceSeparationData

theorem paper_xi_holography_coherence_separation
    (D : XiHolographyCoherenceSeparationData) :
    D.linearEvidenceRate ∧ D.zeroConditionalInformationRate := by
  refine ⟨D.exactGap, ?_⟩
  exact ⟨D.overhead, D.complexityBound⟩

end Omega.Zeta
