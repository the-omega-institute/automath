import Mathlib.Tactic

namespace Omega.Discussion

section CharacterIndexHolonomy

variable {A : Type*} [AddGroup A]

/-- Minimal cocycle holonomy readout used for the character-postcomposition corollary. -/
def characterHolonomy (ℓ : A →+ ℤ) (g : A) : ℤ :=
  ℓ g

/-- Minimal index pairing carried by the same additive cocycle. -/
def characterIndexPairing (ℓ : A →+ ℤ) (g : A) : ℤ :=
  characterHolonomy ℓ g

/-- The chapter-local holonomy/index theorem in this seed model is the identity between the two
readouts. -/
theorem character_index_holonomy_base (ℓ : A →+ ℤ) (g : A) :
    characterIndexPairing ℓ g = characterHolonomy ℓ g := by
  rfl

/-- Postcomposing the cocycle with a character `χ : ℤ →+ ℤ` is functorial on the holonomy
readout. -/
theorem characterHolonomy_postcompose (χ : ℤ →+ ℤ) (ℓ : A →+ ℤ) (g : A) :
    characterHolonomy (χ.comp ℓ) g = χ (characterHolonomy ℓ g) := by
  rfl

/-- Postcomposing the cocycle with a character `χ : ℤ →+ ℤ` is functorial on the index pairing. -/
theorem characterIndexPairing_postcompose (χ : ℤ →+ ℤ) (ℓ : A →+ ℤ) (g : A) :
    characterIndexPairing (χ.comp ℓ) g = χ (characterIndexPairing ℓ g) := by
  rfl

/-- Postcomposing the cocycle `ℓ` with a character `χ : ℤ →+ ℤ` carries the same holonomy/index
pairing theorem to the `χ`-coordinate system.
    cor:discussion-character-index-holonomy -/
theorem paper_discussion_character_index_holonomy
    (χ : ℤ →+ ℤ) (ℓ : A →+ ℤ) (g : A) :
    characterIndexPairing (χ.comp ℓ) g = characterHolonomy (χ.comp ℓ) g ∧
      characterHolonomy (χ.comp ℓ) g = χ (characterHolonomy ℓ g) ∧
      characterIndexPairing (χ.comp ℓ) g = χ (characterIndexPairing ℓ g) := by
  refine ⟨character_index_holonomy_base (χ.comp ℓ) g, ?_, ?_⟩
  · exact characterHolonomy_postcompose χ ℓ g
  · exact characterIndexPairing_postcompose χ ℓ g

end CharacterIndexHolonomy

end Omega.Discussion
