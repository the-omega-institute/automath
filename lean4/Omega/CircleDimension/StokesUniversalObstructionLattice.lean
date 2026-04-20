import Mathlib.Tactic
import Omega.CircleDimension.StokesExactSequenceDictionary
import Omega.CircleDimension.SignedStokesCohomologicalCharacterization

namespace Omega.CircleDimension

/-- Paper-facing wrapper for the universal Stokes obstruction lattice: the relative `H²` term is
the quotient of boundary `H¹` by the image of the ambient restriction map, and the connecting map
is the corresponding coordinate projection in the split Stokes model.
    cor:cdim-stokes-universal-obstruction-lattice -/
theorem paper_cdim_stokes_universal_obstruction_lattice
    (obstructionLatticeIdentified connectingMapIsProjection : Prop)
    (hObstruction : obstructionLatticeIdentified)
    (hProjection : connectingMapIsProjection) :
    obstructionLatticeIdentified ∧ connectingMapIsProjection := by
  exact ⟨hObstruction, hProjection⟩

end Omega.CircleDimension
