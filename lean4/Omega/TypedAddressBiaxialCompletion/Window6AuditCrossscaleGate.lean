import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- Boundary uplift delta set recorded by the window-6 audit. -/
def window6BoundaryDeltaSet : Nat → Finset Nat
  | 6 => ([0, 34] : List Nat).toFinset
  | 7 => ([0, 55, 89] : List Nat).toFinset
  | 8 => ([0, 89, 144] : List Nat).toFinset
  | _ => ∅

/-- A relocking gate for the boundary uplift audit is present exactly when the audited delta set is
nonempty. -/
def HasWindow6RelockingGate (m : Nat) : Prop :=
  (window6BoundaryDeltaSet m).Nonempty

/-- A relocked boundary parity witness must come from one of the audited boundary deltas. -/
def HasWindow6RelockedParity (m : Nat) : Prop :=
  ∃ δ : Nat, δ ∈ window6BoundaryDeltaSet m ∧ δ % 2 = m % 2

/-- Paper wrapper for the audited boundary delta sets at `m = 6, 7, 8`: without an explicit
relocking gate there is no certified relocked parity witness.
    prop:typed-address-biaxial-completion-window6-audit-crossscale-gate -/
theorem paper_typed_address_biaxial_completion_window6_audit_crossscale_gate :
    window6BoundaryDeltaSet 6 = ([0, 34] : List Nat).toFinset ∧
      window6BoundaryDeltaSet 7 = ([0, 55, 89] : List Nat).toFinset ∧
      window6BoundaryDeltaSet 8 = ([0, 89, 144] : List Nat).toFinset ∧
      ∀ m : Nat, ¬ HasWindow6RelockingGate m → ¬ HasWindow6RelockedParity m := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro m hgate hparity
  rcases hparity with ⟨δ, hδ, _⟩
  exact hgate ⟨δ, hδ⟩

end Omega.TypedAddressBiaxialCompletion
