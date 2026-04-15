import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- A chapter-local inverse system over scale-indexed objects. -/
def IsInverseSystem
    (X : Nat → Type)
    (pi : ∀ {hi lo : Nat}, lo ≤ hi → X hi → X lo) : Prop :=
  (∀ {m : Nat} (x : X m), pi (show m ≤ m from le_rfl) x = x) ∧
    ∀ {k m n : Nat} (hnm : n ≤ m) (hmk : m ≤ k) (x : X k),
      pi hnm (pi hmk x) = pi (Nat.le_trans hnm hmk) x

/-- A coherent thread through a scale-indexed inverse system. -/
def InverseLimit
    (X : Nat → Type)
    (pi : ∀ {hi lo : Nat}, lo ≤ hi → X hi → X lo) : Type :=
  { x : ∀ m : Nat, X m // ∀ {hi lo : Nat} (h : lo ≤ hi), pi h (x hi) = x lo }

/-- Minimal chapter-local ontology claim with scale restriction maps. -/
structure MultiscaleOntologyClaim where
  X : Nat → Type
  restrict : ∀ {hi lo : Nat}, lo ≤ hi → X hi → X lo
  restrict_refl : ∀ {m : Nat} (x : X m), restrict (show m ≤ m from le_rfl) x = x
  restrict_comp :
    ∀ {k m n : Nat} (hnm : n ≤ m) (hmk : m ≤ k) (x : X k),
      restrict hnm (restrict hmk x) = restrict (Nat.le_trans hnm hmk) x

/-- A single object persists across every scale and is compatible with the restriction maps. -/
def MultiscaleOntologyClaim.sameObjectAcrossScales (C : MultiscaleOntologyClaim) : Prop :=
  ∃ x : ∀ m : Nat, C.X m,
    ∀ {hi lo : Nat} (h : lo ≤ hi), C.restrict h (x hi) = x lo

set_option maxHeartbeats 400000 in
/-- Paper-facing necessity theorem: scale-consistent addressing supplies a concrete inverse system
and a compatible inverse-limit witness.
    prop:typed-address-biaxial-completion-multiscale-threshold -/
theorem paper_typed_address_biaxial_completion_multiscale_threshold (C : MultiscaleOntologyClaim) :
    C.sameObjectAcrossScales -> ∃ pi : ∀ {m' m : Nat}, m <= m' -> C.X m' -> C.X m,
      IsInverseSystem C.X pi ∧ Nonempty (InverseLimit C.X pi) := by
  intro hsame
  refine ⟨fun {m' m} h => C.restrict h, ?_⟩
  refine ⟨?_, ?_⟩
  · exact ⟨fun {m} x => C.restrict_refl x, fun hnm hmk x => C.restrict_comp hnm hmk x⟩
  · rcases hsame with ⟨x, hx⟩
    refine ⟨⟨x, fun {hi lo} h => hx h⟩⟩

end Omega.TypedAddressBiaxialCompletion
