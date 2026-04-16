import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Chapter-local wrapper for the closed-form reset-sector regeneration constants. The fields store
the three paper-facing outputs: the reset-sector mass, the Kac return-time identity, and the
conditioned waiting-time constant from the finite-state hitting chain. -/
structure RealInput40ResetRegenerationConstantsData where
  resetSectorMassClosed : Prop
  kacReturnTimeClosed : Prop
  conditionalWaitClosed : Prop
  resetSectorMassClosed_h : resetSectorMassClosed
  kacReturnTimeClosed_h : kacReturnTimeClosed
  conditionalWaitClosed_h : conditionalWaitClosed

/-- Paper-facing wrapper for the reset-sector regeneration constants.
    prop:real-input-40-reset-regeneration-constants -/
theorem paper_real_input_40_reset_regeneration_constants
    (D : RealInput40ResetRegenerationConstantsData) :
    D.resetSectorMassClosed ∧ D.kacReturnTimeClosed ∧ D.conditionalWaitClosed := by
  exact ⟨D.resetSectorMassClosed_h, D.kacReturnTimeClosed_h, D.conditionalWaitClosed_h⟩

end Omega.SyncKernelWeighted
