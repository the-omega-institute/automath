import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-tropicalization-completeness`. -/
theorem paper_xi_time_tropicalization_completeness
    (semiringAxioms tropicalFactorization finitePositiveCone gaugeEquivalentValuations : Prop)
    (hAxioms : semiringAxioms) (hFactor : semiringAxioms → tropicalFactorization)
    (hCone : tropicalFactorization → finitePositiveCone)
    (hGauge : finitePositiveCone → gaugeEquivalentValuations) :
    tropicalFactorization ∧ finitePositiveCone ∧ gaugeEquivalentValuations := by
  have hTropical : tropicalFactorization := hFactor hAxioms
  have hCone' : finitePositiveCone := hCone hTropical
  exact ⟨hTropical, hCone', hGauge hCone'⟩

end Omega.Zeta
