import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- Chapter-local audit package for the biaxial completeness gap. A `NULL` readout failure exposes
the three certificates that remain to be supplied: mode stability, residue quota, and endpoint
resolution. -/
structure CompletenessGapAuditData where
  nullReadout : Prop
  modeStabilityCert : Prop
  residueQuotaCert : Prop
  endpointResolutionGate : Prop
  nullImpliesModeStability : nullReadout → modeStabilityCert
  nullImpliesResidueQuota : nullReadout → residueQuotaCert
  nullImpliesEndpointResolution : nullReadout → endpointResolutionGate

/-- A `NULL` readout packages the biaxial completeness gap into the three advertised audit gates.
    prop:typed-address-biaxial-completion-completeness-gap-audit -/
theorem paper_typed_address_biaxial_completion_completeness_gap_audit
    (h : CompletenessGapAuditData) :
    h.nullReadout → h.modeStabilityCert ∧ h.residueQuotaCert ∧ h.endpointResolutionGate := by
  intro hnull
  exact
    ⟨h.nullImpliesModeStability hnull, h.nullImpliesResidueQuota hnull,
      h.nullImpliesEndpointResolution hnull⟩

end Omega.TypedAddressBiaxialCompletion
