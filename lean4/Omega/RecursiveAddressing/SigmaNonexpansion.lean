import Omega.SPG.ScanErrorDiscrete

namespace Omega.RecursiveAddressing.SigmaNonexpansion

/-- The family of events determined by a given observation. -/
def ObservableEventFamily {α β : Type*} (obs : α → β) : Set (Set α) :=
  {S | ∃ A : Set β, S = Omega.SPG.observableEvent obs A}

/-- Postcomposing an observation with a second readout does not create new observable events:
    every event seen after the extra readout is already the pullback of an old observable event. -/
theorem observableEvent_postcompose
    {α β γ : Type*} (obs : α → β) (refine : β → γ) (A : Set γ) :
    Omega.SPG.observableEvent (refine ∘ obs) A =
      Omega.SPG.observableEvent obs (refine ⁻¹' A) := by
  ext x
  simp [Omega.SPG.observableEvent]

/-- The observable-event family can only shrink under postcomposition. -/
theorem observableEventFamily_postcompose_subset
    {α β γ : Type*} (obs : α → β) (refine : β → γ) :
    ObservableEventFamily (refine ∘ obs) ⊆ ObservableEventFamily obs := by
  intro S hS
  rcases hS with ⟨A, rfl⟩
  exact ⟨refine ⁻¹' A, observableEvent_postcompose obs refine A⟩

/-- Paper-facing seeds for `cor:sigma-nonexpansion`.
    If level `L + 1` is read from level `L` by postcomposition, then every new visible event is
    already visible at level `L`. -/
theorem paper_scan_projection_address_sigma_nonexpansion_seeds
    {α β γ : Type*} (obsL : α → β) (Φ : β → γ) :
    (∀ A : Set γ,
      Omega.SPG.observableEvent (Φ ∘ obsL) A =
        Omega.SPG.observableEvent obsL (Φ ⁻¹' A)) ∧
    ObservableEventFamily (Φ ∘ obsL) ⊆ ObservableEventFamily obsL := by
  constructor
  · intro A
    exact observableEvent_postcompose obsL Φ A
  · exact observableEventFamily_postcompose_subset obsL Φ

/-- Packaged form of the `cor:sigma-nonexpansion` seeds. -/
theorem paper_scan_projection_address_sigma_nonexpansion_package
    {α β γ : Type*} (obsL : α → β) (Φ : β → γ) :
    (∀ A : Set γ,
      Omega.SPG.observableEvent (Φ ∘ obsL) A =
        Omega.SPG.observableEvent obsL (Φ ⁻¹' A)) ∧
    ObservableEventFamily (Φ ∘ obsL) ⊆ ObservableEventFamily obsL :=
  paper_scan_projection_address_sigma_nonexpansion_seeds obsL Φ

end Omega.RecursiveAddressing.SigmaNonexpansion
