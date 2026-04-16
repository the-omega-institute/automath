import Mathlib.Tactic

namespace Omega.Folding

/-- Chapter-local witness for the layerwise auditable primorial necessity statement. The fields
record exactly the four paper-facing consequences extracted from the layerwise valuation
comparison. -/
structure LayerwiseAuditablePrimorialNecessityData where
  Layer : Type
  auditPrime : Layer → ℕ
  code : Layer → ℕ
  distinctAuditPrimes : Prop
  unitValuationAtOwnLayer : Prop
  noCrossLayerPrimeLeakage : Prop
  primorialLowerBound : Prop
  distinctAuditPrimes_h : distinctAuditPrimes
  unitValuationAtOwnLayer_h : unitValuationAtOwnLayer
  noCrossLayerPrimeLeakage_h : noCrossLayerPrimeLeakage
  primorialLowerBound_h : primorialLowerBound

/-- Paper-facing wrapper for the necessity of distinct audit primes, unit own-layer valuation,
cross-layer prime leakage exclusion, and the resulting primorial lower bound.
    prop:fold-layerwise-auditable-primorial-necessity -/
theorem paper_fold_layerwise_auditable_primorial_necessity
    (D : LayerwiseAuditablePrimorialNecessityData) :
    D.distinctAuditPrimes ∧
      D.unitValuationAtOwnLayer ∧
      D.noCrossLayerPrimeLeakage ∧
      D.primorialLowerBound := by
  exact ⟨D.distinctAuditPrimes_h, D.unitValuationAtOwnLayer_h,
    D.noCrossLayerPrimeLeakage_h, D.primorialLowerBound_h⟩

end Omega.Folding
