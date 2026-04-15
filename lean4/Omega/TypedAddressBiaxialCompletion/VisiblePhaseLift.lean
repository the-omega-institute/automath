import Omega.TypedAddressBiaxialCompletion.MultiscaleThreshold

namespace Omega.TypedAddressBiaxialCompletion

set_option maxHeartbeats 400000 in
/-- A compatible family defines the unique point of the chapter-local inverse limit.
    prop:typed-address-biaxial-completion-visible-phase-lift -/
theorem paper_typed_address_biaxial_completion_visible_phase_lift
    (X : Nat → Type) (pi : ∀ {hi lo : Nat}, lo ≤ hi → X hi → X lo) (hpi : IsInverseSystem X pi)
    (theta : ∀ b : Nat, X b)
    (htheta : ∀ {hi lo : Nat} (h : lo ≤ hi), pi h (theta hi) = theta lo) :
    ∃! u : InverseLimit X pi, ∀ b : Nat, u.1 b = theta b := by
  let _ := hpi
  refine ⟨⟨theta, fun {hi lo} h => htheta h⟩, ?_, ?_⟩
  · intro b
    rfl
  · intro u hu
    apply Subtype.ext
    funext b
    exact hu b

end Omega.TypedAddressBiaxialCompletion
