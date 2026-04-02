import Mathlib.Tactic

namespace Omega.EA

def projectorVal (α β a b : Int) : Int :=
  ((1 + α * a) * (1 + β * b)) / 4

/-- The four sign projectors partition unity on ±1 inputs.
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem projectorVal_partition_of_signs
    {a b : Int} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    projectorVal 1 1 a b + projectorVal 1 (-1) a b +
    projectorVal (-1) 1 a b + projectorVal (-1) (-1) a b = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num [projectorVal]

/-- Exactly one projector takes value 1 on any ±1 sign pattern.
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem projectorVal_case_split
    {a b : Int} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    projectorVal 1 1 a b = 1 ∨ projectorVal 1 (-1) a b = 1 ∨
    projectorVal (-1) 1 a b = 1 ∨ projectorVal (-1) (-1) a b = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num [projectorVal]

/-- The `(+,-)` projector is idempotent on sign inputs.
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem epn_idempotent
    {a b : Int} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    projectorVal 1 (-1) a b * projectorVal 1 (-1) a b = projectorVal 1 (-1) a b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num [projectorVal]

/-- The `(-,+)` projector is idempotent on sign inputs.
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem enp_idempotent
    {a b : Int} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    projectorVal (-1) 1 a b * projectorVal (-1) 1 a b = projectorVal (-1) 1 a b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num [projectorVal]

/-- The `(-,-)` projector is idempotent on sign inputs.
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem enn_idempotent
    {a b : Int} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    projectorVal (-1) (-1) a b * projectorVal (-1) (-1) a b = projectorVal (-1) (-1) a b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num [projectorVal]

end Omega.EA
