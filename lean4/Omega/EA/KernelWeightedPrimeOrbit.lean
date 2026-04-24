import Mathlib.Tactic

namespace Omega.EA

/-- The weighted prime-orbit conclusion is the direct package obtained from the trace formula, the
spectral-gap control, and the wrapper deriving the asymptotic from those two inputs.
    thm:kernel-weighted-prime-orbit -/
theorem paper_kernel_weighted_prime_orbit
    (traceFormula spectralGapControl weightedPrimeOrbitAsymptotic : Prop) :
    traceFormula → spectralGapControl →
      (traceFormula → spectralGapControl → weightedPrimeOrbitAsymptotic) →
        traceFormula ∧ spectralGapControl ∧ weightedPrimeOrbitAsymptotic := by
  intro hTrace hGap hAsymptotic
  exact ⟨hTrace, hGap, hAsymptotic hTrace hGap⟩

end Omega.EA
