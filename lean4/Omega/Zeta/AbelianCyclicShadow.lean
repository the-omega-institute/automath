import Omega.Zeta.QuotientFunctoriality

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the abelian/cyclic shadow corollary in the ETDS shadow section.
    cor:abelian-cyclic-shadow -/
theorem paper_etds_abelian_cyclic_shadow
    (logFunctoriality primitiveFunctoriality quotientClassDecomposition
      oneDimensionalPullback cyclicLayerRecovery cyclicQuotientDescription : Prop)
    (hLog : logFunctoriality)
    (hPrimitive : logFunctoriality → primitiveFunctoriality)
    (hClasses : primitiveFunctoriality → quotientClassDecomposition)
    (hOneDim : quotientClassDecomposition → oneDimensionalPullback)
    (hCyclic : oneDimensionalPullback → cyclicLayerRecovery)
    (hQuotient : cyclicLayerRecovery → cyclicQuotientDescription) :
    oneDimensionalPullback ∧ cyclicLayerRecovery ∧ cyclicQuotientDescription := by
  have hFunctoriality :=
    paper_etds_quotient_functoriality
      logFunctoriality primitiveFunctoriality quotientClassDecomposition
      hLog hPrimitive hClasses
  have hOneDimensional : oneDimensionalPullback := hOneDim hFunctoriality.2.2
  have hCyclicRecovery : cyclicLayerRecovery := hCyclic hOneDimensional
  exact ⟨hOneDimensional, hCyclicRecovery, hQuotient hCyclicRecovery⟩

end Omega.Zeta
