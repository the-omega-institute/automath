import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-profinite-artin-hilbert`. -/
theorem paper_pom_profinite_artin_hilbert
    (operatorPerpRadius twistedSup trivialRadius bound : ℝ)
    (hBlockRadius : operatorPerpRadius = twistedSup) (_hTrivialRadius : 0 ≤ trivialRadius)
    (hKernelGRH : twistedSup ≤ bound) :
    operatorPerpRadius ≤ bound := by
  simpa [hBlockRadius] using hKernelGRH

end Omega.POM
