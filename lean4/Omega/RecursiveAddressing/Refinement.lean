import Omega.RecursiveAddressing.SigmaNonexpansion

namespace Omega.RecursiveAddressing

/-- Paper: `prop:recursive-addressing-refinement`.
    Any derived cylinder event obtained by postcomposing the old-layer observation is already an
    observable event for the old layer itself. -/
theorem paper_recursive_addressing_refinement
    {α β γ : Type*} (obsL : α → β) (Φ : β → γ) (A : Set γ) :
    Omega.SPG.observableEvent (Φ ∘ obsL) A ∈
      Omega.RecursiveAddressing.SigmaNonexpansion.ObservableEventFamily obsL := by
  exact ⟨Φ ⁻¹' A, SigmaNonexpansion.observableEvent_postcompose obsL Φ A⟩

end Omega.RecursiveAddressing
