import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic

namespace Omega.GroupUnification

structure BdryOrientationLocalSystemData where
  degree : ℕ
  monodromy : Equiv.Perm (Fin degree)
  determinantCharacter : Units ℤ
  determinantCharacter_eq_sign : determinantCharacter = Equiv.Perm.sign monodromy

def bdryOrientationJumpclassVanishes (D : BdryOrientationLocalSystemData) : Prop :=
  D.determinantCharacter = 1

def bdryOrientationGlobalSection (D : BdryOrientationLocalSystemData) : Prop :=
  D.determinantCharacter = 1

def bdryOrientationAlternatingReduction (D : BdryOrientationLocalSystemData) : Prop :=
  Equiv.Perm.sign D.monodromy = 1

def BdryOrientationLocalSystemData.statement (D : BdryOrientationLocalSystemData) : Prop :=
  (bdryOrientationJumpclassVanishes D ↔ bdryOrientationGlobalSection D) ∧
    (bdryOrientationJumpclassVanishes D ↔ bdryOrientationAlternatingReduction D)

/-- Paper label: `cor:bdry-orientation-local-system-w1-alternating-reduction`.
The determinant/sign character simultaneously records the jumpclass, the obstruction to a global
section of the orientation local system, and the reduction of monodromy to the alternating group. -/
theorem paper_bdry_orientation_local_system_w1_alternating_reduction_structured
    (D : BdryOrientationLocalSystemData) : D.statement := by
  refine ⟨Iff.rfl, ?_⟩
  constructor
  · intro hJump
    unfold bdryOrientationJumpclassVanishes bdryOrientationAlternatingReduction at *
    rw [D.determinantCharacter_eq_sign] at hJump
    exact hJump
  · intro hAlt
    unfold bdryOrientationJumpclassVanishes bdryOrientationAlternatingReduction at *
    rw [D.determinantCharacter_eq_sign]
    exact hAlt

end Omega.GroupUnification
