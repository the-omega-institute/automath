import Omega.RecursiveAddressing.SigmaNonexpansion

namespace Omega.RecursiveAddressing

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: postcomposing the visible readout cannot enlarge the family of observable
events.
    cor:recursive-addressing-visible-sigma-nonexpansion -/
theorem paper_recursive_addressing_visible_sigma_nonexpansion_seeds
    {α β γ : Type*} (obsL : α → β) (Φ : β → γ) :
    SigmaNonexpansion.ObservableEventFamily (Φ ∘ obsL) ⊆
      SigmaNonexpansion.ObservableEventFamily obsL :=
  SigmaNonexpansion.observableEventFamily_postcompose_subset obsL Φ

/-- Packaged form of the visible-σ nonexpansion seed.
    cor:recursive-addressing-visible-sigma-nonexpansion -/
theorem paper_recursive_addressing_visible_sigma_nonexpansion_package
    {α β γ : Type*} (obsL : α → β) (Φ : β → γ) :
    SigmaNonexpansion.ObservableEventFamily (Φ ∘ obsL) ⊆
      SigmaNonexpansion.ObservableEventFamily obsL :=
  paper_recursive_addressing_visible_sigma_nonexpansion_seeds obsL Φ

/-- Unsuffixed paper-facing wrapper matching the paper label.
    cor:recursive-addressing-visible-sigma-nonexpansion -/
theorem paper_recursive_addressing_visible_sigma_nonexpansion
    {α β γ : Type*} (obsL : α → β) (Φ : β → γ) :
    SigmaNonexpansion.ObservableEventFamily (Φ ∘ obsL) ⊆
      SigmaNonexpansion.ObservableEventFamily obsL :=
  paper_recursive_addressing_visible_sigma_nonexpansion_package obsL Φ

end Omega.RecursiveAddressing
