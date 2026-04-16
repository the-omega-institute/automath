import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- The three irreducible boundary-budget axes appearing in the biaxial completion readout. -/
structure BoundaryBudgetAxes where
  radiusBlindspotClosed : Prop
  addressCollisionClosed : Prop
  endpointHeatClosed : Prop

/-- Abstract output of the chapter-local boundary verifier. -/
inductive BoundaryVerifierResult where
  | null
  | certificate
  deriving DecidableEq

/-- Minimal interface for the joint sufficiency theorem: simultaneous closure of the three
boundary axes and the Toeplitz--PSD side condition yields a non-`NULL` certificate, while each
axis remains logically non-substitutable by the other two. -/
structure BoundaryJointVerifierData where
  axes : BoundaryBudgetAxes
  toeplitzPsdPassed : Prop
  verifierResult : BoundaryVerifierResult
  accepts_of_jointClosure :
    axes.radiusBlindspotClosed →
      axes.addressCollisionClosed →
        axes.endpointHeatClosed →
          toeplitzPsdPassed →
            verifierResult = .certificate
  radius_required :
    verifierResult = .certificate → axes.radiusBlindspotClosed
  address_required :
    verifierResult = .certificate → axes.addressCollisionClosed
  endpoint_required :
    verifierResult = .certificate → axes.endpointHeatClosed
  radius_non_substitutable :
    axes.addressCollisionClosed →
      axes.endpointHeatClosed →
        ¬ axes.radiusBlindspotClosed →
          verifierResult ≠ .certificate
  address_non_substitutable :
    axes.radiusBlindspotClosed →
      axes.endpointHeatClosed →
        ¬ axes.addressCollisionClosed →
          verifierResult ≠ .certificate
  endpoint_non_substitutable :
    axes.radiusBlindspotClosed →
      axes.addressCollisionClosed →
        ¬ axes.endpointHeatClosed →
          verifierResult ≠ .certificate

/-- Joint closure of the radius, address, and endpoint-heat axes is sufficient for a non-`NULL`
boundary certificate, and none of the three axes can be replaced by the other two.
    thm:typed-address-biaxial-completion-boundary-joint-sufficiency -/
theorem paper_typed_address_biaxial_completion_boundary_joint_sufficiency
    (h : BoundaryJointVerifierData) :
    (h.axes.radiusBlindspotClosed ∧ h.axes.addressCollisionClosed ∧
        h.axes.endpointHeatClosed ∧ h.toeplitzPsdPassed →
      h.verifierResult = .certificate) ∧
    (h.verifierResult = .certificate →
      h.axes.radiusBlindspotClosed ∧
        h.axes.addressCollisionClosed ∧
        h.axes.endpointHeatClosed) ∧
    ((h.axes.addressCollisionClosed ∧ h.axes.endpointHeatClosed ∧
        ¬ h.axes.radiusBlindspotClosed) →
      h.verifierResult ≠ .certificate) ∧
    ((h.axes.radiusBlindspotClosed ∧ h.axes.endpointHeatClosed ∧
        ¬ h.axes.addressCollisionClosed) →
      h.verifierResult ≠ .certificate) ∧
    ((h.axes.radiusBlindspotClosed ∧ h.axes.addressCollisionClosed ∧
        ¬ h.axes.endpointHeatClosed) →
      h.verifierResult ≠ .certificate) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨hr, ha, he, hpsd⟩
    exact h.accepts_of_jointClosure hr ha he hpsd
  · intro hcert
    exact ⟨h.radius_required hcert, h.address_required hcert, h.endpoint_required hcert⟩
  · rintro ⟨ha, he, hnotr⟩
    exact h.radius_non_substitutable ha he hnotr
  · rintro ⟨hr, he, hnota⟩
    exact h.address_non_substitutable hr he hnota
  · rintro ⟨hr, ha, hnote⟩
    exact h.endpoint_non_substitutable hr ha hnote

end Omega.TypedAddressBiaxialCompletion
