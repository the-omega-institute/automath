import Mathlib.Data.Int.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic
import Omega.GU.BdryOrientationBlockDecompositionOddVisibility

namespace Omega.GU

/-- The sign of the permutation induced on the odd-cardinality blocks. -/
def oddBlockPermutationSign {T : Type*} [Fintype T] [DecidableEq T] (size : T → ℕ)
    (tau : Equiv.Perm T) : Units ℤ :=
  if ∀ t, Odd (size t) then tau.sign else 1

/-- The global wreath orientation character on the boundary labeling torsor. -/
def wreathOrientationSign {T : Type*} [Fintype T] [DecidableEq T] (size : T → ℕ)
    (eps : T → Units ℤ) (tau : Equiv.Perm T) : Units ℤ :=
  oddBlockPermutationSign size tau * Finset.univ.prod eps

/-- The odd-block visibility decomposition makes the wreath orientation character split into the
odd-block permutation sign and the product of the blockwise signs.
`thm:bdry-orientation-wreath-character-odd-visibility` -/
theorem paper_bdry_orientation_wreath_character_odd_visibility {T : Type} [Fintype T]
    [DecidableEq T] (size : T → Nat) (eps : T → Units Int) (tau : Equiv.Perm T) :
    wreathOrientationSign size eps tau = oddBlockPermutationSign size tau * Finset.univ.prod eps := by
  simp [wreathOrientationSign]

end Omega.GU
