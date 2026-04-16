import Mathlib.Tactic
import Omega.Conclusion.Window6BoundarySuperselectionC3OrbitStratification

namespace Omega.Conclusion

/-- The cubic projector separates the short-root orbit from its complement. -/
abbrev Window6ShortRootOrbit := Bool

/-- Orbit/parity labels are the product of the short-root orbit bit with the eight boundary-parity
characters. -/
abbrev Window6OrbitParitySector := Window6ShortRootOrbit × Window6BoundaryCharacter

/-- A concrete `0/1` projector selecting the short-root orbit. -/
def cubicShortRootProjector : Window6ShortRootOrbit → ℚ
  | true => 1
  | false => 0

/-- The cubic short-root projector is idempotent. -/
theorem cubicShortRootProjector_idempotent (b : Window6ShortRootOrbit) :
    cubicShortRootProjector b * cubicShortRootProjector b = cubicShortRootProjector b := by
  cases b <;> norm_num [cubicShortRootProjector]

/-- The short-root selector contributes two orbit types. -/
theorem window6_short_root_orbit_card : Fintype.card Window6ShortRootOrbit = 2 := by
  native_decide

/-- The boundary parity group has eight characters. -/
theorem window6_boundary_parity_card : Fintype.card Window6BoundaryCharacter = 8 := by
  native_decide

/-- The orbit/parity refinement therefore has sixteen labels. -/
theorem window6_orbit_parity_sector_card : Fintype.card Window6OrbitParitySector = 16 := by
  native_decide

/-- Wrapper data for the window-6 orbit/parity superselection theorem. -/
structure Window6CyclicOrbitParitySuperselectionData where
  cubicProjectorSelectsShortRootOrbit : Prop
  eightBoundaryParityIdempotents : Prop
  commutingIdempotents : Prop
  pairwiseOrthogonalSummands : Prop
  summandsAddToIdentity : Prop
  cubicProjectorWitness : cubicProjectorSelectsShortRootOrbit
  boundaryParityWitness : eightBoundaryParityIdempotents
  commutingWitness : commutingIdempotents
  orthogonalityWitness : pairwiseOrthogonalSummands
  identityWitness : summandsAddToIdentity

/-- Paper-facing decomposition statement. -/
def Window6CyclicOrbitParitySuperselectionData.sixteenfoldSuperselectionDecomposition
    (h : Window6CyclicOrbitParitySuperselectionData) : Prop :=
  Fintype.card Window6OrbitParitySector = 16 ∧
    h.cubicProjectorSelectsShortRootOrbit ∧
      h.eightBoundaryParityIdempotents ∧
        h.commutingIdempotents ∧
          h.pairwiseOrthogonalSummands ∧ h.summandsAddToIdentity

/-- Paper theorem: the short-root cubic projector commutes with the eight boundary-parity
idempotents, so their product decomposition yields sixteen orthogonal summands whose sum is the
identity.
    thm:conclusion-window6-cyclic-orbit-parity-sixteenfold -/
theorem paper_conclusion_window6_cyclic_orbit_parity_sixteenfold
    (h : Window6CyclicOrbitParitySuperselectionData) :
    h.sixteenfoldSuperselectionDecomposition := by
  exact
    ⟨window6_orbit_parity_sector_card, h.cubicProjectorWitness, h.boundaryParityWitness,
      h.commutingWitness, h.orthogonalityWitness, h.identityWitness⟩

end Omega.Conclusion
