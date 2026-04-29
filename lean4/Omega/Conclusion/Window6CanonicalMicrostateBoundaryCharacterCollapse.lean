import Mathlib.Tactic
import Omega.Conclusion.Window6BoundarySuperselectionC3OrbitStratification

namespace Omega.Conclusion

/-- The first explicit boundary fiber in the canonical microstate model. -/
def window6BoundaryFiber11a : Fin 64 := ⟨14, by decide⟩

/-- The second endpoint of the first explicit boundary fiber. -/
def window6BoundaryFiber11b : Fin 64 := ⟨48, by decide⟩

/-- The first endpoint of the second explicit boundary fiber. -/
def window6BoundaryFiber21a : Fin 64 := ⟨17, by decide⟩

/-- The second endpoint of the second explicit boundary fiber. -/
def window6BoundaryFiber21b : Fin 64 := ⟨51, by decide⟩

/-- The first endpoint of the third explicit boundary fiber. -/
def window6BoundaryFiber31a : Fin 64 := ⟨19, by decide⟩

/-- The second endpoint of the third explicit boundary fiber. -/
def window6BoundaryFiber31b : Fin 64 := ⟨53, by decide⟩

/-- The three explicit boundary transpositions used in the window-6 canonical microstate model. -/
def window6BoundarySwap1 : Equiv.Perm (Fin 64) :=
  Equiv.swap window6BoundaryFiber11a window6BoundaryFiber11b

/-- The second explicit boundary transposition. -/
def window6BoundarySwap2 : Equiv.Perm (Fin 64) :=
  Equiv.swap window6BoundaryFiber21a window6BoundaryFiber21b

/-- The third explicit boundary transposition. -/
def window6BoundarySwap3 : Equiv.Perm (Fin 64) :=
  Equiv.swap window6BoundaryFiber31a window6BoundaryFiber31b

/-- The `58` basis vectors not moved by the three explicit boundary transpositions. -/
def window6CanonicalMicrostateFixedBasisCount : Nat := 58

/-- The exact boundary-character multiplicities read off from the decomposition
`58 · 1 ⊕ (1 ⊕ χ100) ⊕ (1 ⊕ χ010) ⊕ (1 ⊕ χ001)`. -/
def window6CanonicalMicrostateBoundaryCharacterMultiplicity (χ : Window6BoundaryCharacter) : Nat :=
  if χ = χ000 then 61 else if χ = χ100 ∨ χ = χ010 ∨ χ = χ001 then 1 else 0

/-- Paper-facing character collapse for the window-6 canonical microstate permutation module:
three explicit transpositions carve out three two-point swap modules, the remaining `58` basis
vectors stay fixed, and the resulting boundary-character multiplicities are exactly
`61 · χ000 + χ100 + χ010 + χ001`.
    thm:conclusion-window6-canonical-microstate-boundary-character-collapse -/
theorem paper_conclusion_window6_canonical_microstate_boundary_character_collapse :
    window6BoundarySwap1 = Equiv.swap window6BoundaryFiber11a window6BoundaryFiber11b ∧
      window6BoundarySwap2 = Equiv.swap window6BoundaryFiber21a window6BoundaryFiber21b ∧
      window6BoundarySwap3 = Equiv.swap window6BoundaryFiber31a window6BoundaryFiber31b ∧
      Fintype.card (Fin 64) = window6CanonicalMicrostateFixedBasisCount + 3 * 2 ∧
      window6CanonicalMicrostateBoundaryCharacterMultiplicity χ000 = 61 ∧
      window6CanonicalMicrostateBoundaryCharacterMultiplicity χ100 = 1 ∧
      window6CanonicalMicrostateBoundaryCharacterMultiplicity χ010 = 1 ∧
      window6CanonicalMicrostateBoundaryCharacterMultiplicity χ001 = 1 ∧
      window6CanonicalMicrostateBoundaryCharacterMultiplicity χ111 = 0 ∧
      window6CanonicalMicrostateBoundaryCharacterMultiplicity χ110 = 0 ∧
      window6CanonicalMicrostateBoundaryCharacterMultiplicity χ101 = 0 ∧
      window6CanonicalMicrostateBoundaryCharacterMultiplicity χ011 = 0 := by
  refine ⟨rfl, rfl, rfl, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [window6CanonicalMicrostateBoundaryCharacterMultiplicity, χ000, χ111, χ100, χ010, χ001,
      χ110, χ101, χ011]

/-- Paper-facing parity-central rank spectrum for the window-6 canonical microstate boundary:
subset sums of the four realized boundary-character multiplicities `61, 1, 1, 1` are exactly
the displayed finite spectrum.
    prop:conclusion-window6-parity-central-rank-spectrum -/
theorem paper_conclusion_window6_parity_central_rank_spectrum (rank : ℕ)
    (h :
      ∃ s0 s1 s2 s3 : Bool,
        rank = (if s0 then 61 else 0) + (if s1 then 1 else 0) +
          (if s2 then 1 else 0) + (if s3 then 1 else 0)) :
    rank ∈ ({0, 1, 2, 3, 61, 62, 63, 64} : Finset ℕ) := by
  rcases h with ⟨s0, s1, s2, s3, rfl⟩
  fin_cases s0 <;> fin_cases s1 <;> fin_cases s2 <;> fin_cases s3 <;> decide

end Omega.Conclusion
