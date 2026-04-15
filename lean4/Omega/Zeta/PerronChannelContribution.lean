import Mathlib

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the Perron-channel contribution estimate in the ETDS
    finite-group section.
    lem:perron-channel-contribution -/
theorem paper_etds_perron_channel_contribution
    (spectralDominance primitiveOrbitAsymptotic tailEstimate correctionIdentity
      perronContribution : Prop)
    (hSpectral : spectralDominance)
    (hAsymptotic : spectralDominance → primitiveOrbitAsymptotic)
    (hTail : primitiveOrbitAsymptotic → tailEstimate)
    (hCorrection : primitiveOrbitAsymptotic → correctionIdentity)
    (hContribution : correctionIdentity → tailEstimate → perronContribution) :
    primitiveOrbitAsymptotic ∧
      tailEstimate ∧
      correctionIdentity ∧
      perronContribution := by
  have hPrimitive : primitiveOrbitAsymptotic := hAsymptotic hSpectral
  have hTail' : tailEstimate := hTail hPrimitive
  have hCorrection' : correctionIdentity := hCorrection hPrimitive
  exact ⟨hPrimitive, hTail', hCorrection', hContribution hCorrection' hTail'⟩

end Omega.Zeta
