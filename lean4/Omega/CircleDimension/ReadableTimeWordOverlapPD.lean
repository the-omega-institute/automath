import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Chapter-local package for the readable-time-word overlap kernel. It isolates the `q = 1`
specialization of the mixed-collision kernel, the explicit `ℓ²` feature map, and the
characteristic-kernel readout used in the Hilbert-carrier chapter. -/
structure ReadableTimeWordOverlapPDData where
  qOneSpecialization : Prop
  mixedCollisionPositiveDefinite : Prop
  l2FeatureMap : Prop
  characteristicKernel : Prop
  pullbackPositiveDefinite : Prop
  characteristicReadout : Prop
  hasQOneSpecialization : qOneSpecialization
  hasMixedCollisionPositiveDefinite : mixedCollisionPositiveDefinite
  hasCharacteristicKernel : characteristicKernel
  defineL2FeatureMap : qOneSpecialization → l2FeatureMap
  derivePullbackPositiveDefinite :
    mixedCollisionPositiveDefinite →
      qOneSpecialization →
        l2FeatureMap →
          pullbackPositiveDefinite
  deriveCharacteristicReadout :
    characteristicKernel →
      qOneSpecialization →
        pullbackPositiveDefinite →
          characteristicReadout

/-- Paper-facing wrapper for the positive-definite overlap kernel on readable time words.
    thm:cdim-readable-time-word-overlap-pd -/
theorem paper_cdim_readable_time_word_overlap_pd (D : ReadableTimeWordOverlapPDData) :
    D.pullbackPositiveDefinite ∧ D.characteristicReadout := by
  have hFeatureMap : D.l2FeatureMap := D.defineL2FeatureMap D.hasQOneSpecialization
  have hPD : D.pullbackPositiveDefinite :=
    D.derivePullbackPositiveDefinite D.hasMixedCollisionPositiveDefinite
      D.hasQOneSpecialization hFeatureMap
  exact ⟨hPD, D.deriveCharacteristicReadout D.hasCharacteristicKernel D.hasQOneSpecialization hPD⟩

end Omega.CircleDimension
