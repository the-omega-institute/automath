import Omega.RecursiveAddressing.SigmaNonexpansion

namespace Omega.RecursiveAddressing

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for measurable refinement in recursive addressing:
    every event visible after a derived finite-window readout is already visible at the previous
    level.
    prop:recursive-addressing-refinement -/
theorem paper_recursive_addressing_refinement
    {α β γ : Type*} (obsL : α → β) (Φ : β → γ) (A : Set γ) :
    Omega.SPG.observableEvent (Φ ∘ obsL) A ∈ SigmaNonexpansion.ObservableEventFamily obsL := by
  exact ⟨Φ ⁻¹' A, SigmaNonexpansion.observableEvent_postcompose obsL Φ A⟩

end Omega.RecursiveAddressing
