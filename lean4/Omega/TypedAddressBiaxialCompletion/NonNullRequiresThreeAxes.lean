import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- Chapter-local package for the three axis checks behind a compiled typed-address readout. The
fields isolate the visible, residue, and mode axis passes together with the assumptions that a
non-`NULL` readout certifies each of them. -/
structure TypedAddressThreeAxisData where
  nonNullReadout : Prop
  visibleAxisPassed : Prop
  residueAxisPassed : Prop
  modeAxisPassed : Prop
  readabilityWitness : nonNullReadout → visibleAxisPassed
  residueWitness : nonNullReadout → residueAxisPassed
  modeWitness : nonNullReadout → modeAxisPassed

/-- Any compiled non-`NULL` readout forces the visible-axis, residue-axis, and mode-axis checks to
have passed simultaneously.
    prop:typed-address-biaxial-completion-nonnull-requires-three-axes -/
theorem paper_typed_address_biaxial_completion_nonnull_requires_three_axes
    (h : TypedAddressThreeAxisData) :
    h.nonNullReadout → h.visibleAxisPassed ∧ h.residueAxisPassed ∧ h.modeAxisPassed := by
  intro hnonnull
  exact
    ⟨h.readabilityWitness hnonnull, h.residueWitness hnonnull, h.modeWitness hnonnull⟩

/-- Paper: `prop:typed-address-biaxial-completion-readability-thresholds`.
Any non-`NULL` readout must clear all three orthogonal readability thresholds. -/
theorem paper_typed_address_biaxial_completion_readability_thresholds
    (h : TypedAddressThreeAxisData) :
    h.nonNullReadout → h.visibleAxisPassed ∧ h.residueAxisPassed ∧ h.modeAxisPassed := by
  exact paper_typed_address_biaxial_completion_nonnull_requires_three_axes h

end Omega.TypedAddressBiaxialCompletion
