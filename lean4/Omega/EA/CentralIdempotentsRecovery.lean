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

/-- Reindexing the four sign projectors still gives a partition of unity on ±1 inputs.
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem projectorVal_sum_eq_one_of_cases
    {α β a b : Int}
    (hα : α = 1 ∨ α = -1) (hβ : β = 1 ∨ β = -1)
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    projectorVal α β a b +
        projectorVal α (-β) a b +
        projectorVal (-α) β a b +
        projectorVal (-α) (-β) a b = 1 := by
  rcases hα with rfl | rfl <;>
    rcases hβ with rfl | rfl <;>
    rcases ha with rfl | rfl <;>
    rcases hb with rfl | rfl <;>
    norm_num [projectorVal]

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

/-- Exact characterization of when a sign projector equals 1.
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem projectorVal_eq_one_iff
    {α β a b : Int}
    (hα : α = 1 ∨ α = -1) (hβ : β = 1 ∨ β = -1)
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    projectorVal α β a b = 1 ↔ a = α ∧ b = β := by
  rcases hα with rfl | rfl <;>
    rcases hβ with rfl | rfl <;>
    rcases ha with rfl | rfl <;>
    rcases hb with rfl | rfl <;>
    norm_num [projectorVal]

/-- On ±1 inputs, a sign projector vanishes exactly when at least one sign mismatches.
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem projectorVal_zero_iff_ne
    {α β a b : Int}
    (hα : α = 1 ∨ α = -1) (hβ : β = 1 ∨ β = -1)
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    projectorVal α β a b = 0 ↔ a ≠ α ∨ b ≠ β := by
  rcases hα with rfl | rfl <;>
    rcases hβ with rfl | rfl <;>
    rcases ha with rfl | rfl <;>
    rcases hb with rfl | rfl <;>
    norm_num [projectorVal]

end Omega.EA
