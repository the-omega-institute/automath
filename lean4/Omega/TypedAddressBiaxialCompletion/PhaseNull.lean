import Omega.TypedAddressBiaxialCompletion.CompiledReadability
import Omega.TypedAddressBiaxialCompletion.VisiblePhaseLift

namespace Omega.TypedAddressBiaxialCompletion

/-- Paper-facing wrapper for the phase-completion `NULL` obstruction: lifting to the visible phase
object does not by itself discharge the address, certificate-depth, record-axis, and type-safety
obligations needed to avoid a `NULL` readout.
    prop:typed-address-biaxial-completion-phase-null -/
theorem paper_typed_address_biaxial_completion_phase_null
    (phaseLifted addressReady certDepthReady recordAxisReady typeSafe nullReadout : Prop)
    (hLift : phaseLifted)
    (hNull : phaseLifted ∧ ¬ (addressReady ∧ certDepthReady ∧ recordAxisReady ∧ typeSafe) →
      nullReadout) :
    phaseLifted ∧
      (¬ (addressReady ∧ certDepthReady ∧ recordAxisReady ∧ typeSafe) → nullReadout) := by
  refine ⟨hLift, ?_⟩
  intro hMissing
  exact hNull ⟨hLift, hMissing⟩

end Omega.TypedAddressBiaxialCompletion
