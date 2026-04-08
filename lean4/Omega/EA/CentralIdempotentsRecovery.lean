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

/-- On ±1 inputs, one projector equals `1` exactly when the other three vanish.
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem projectorVal_eq_one_iff_other_three_zero
    {α β a b : Int}
    (hα : α = 1 ∨ α = -1) (hβ : β = 1 ∨ β = -1)
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    projectorVal α β a b = 1 ↔
      projectorVal α (-β) a b = 0 ∧
      projectorVal (-α) β a b = 0 ∧
      projectorVal (-α) (-β) a b = 0 := by
  rcases hα with rfl | rfl <;>
    rcases hβ with rfl | rfl <;>
    rcases ha with rfl | rfl <;>
    rcases hb with rfl | rfl <;>
    norm_num [projectorVal]

/-- On ±1 inputs, if one projector vanishes then one of the other three equals `1`.
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem projectorVal_zero_iff_other_exists_one
    {α β a b : Int}
    (hα : α = 1 ∨ α = -1) (hβ : β = 1 ∨ β = -1)
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    projectorVal α β a b = 0 ↔
      projectorVal α (-β) a b = 1 ∨
      projectorVal (-α) β a b = 1 ∨
      projectorVal (-α) (-β) a b = 1 := by
  rcases hα with rfl | rfl <;>
    rcases hβ with rfl | rfl <;>
    rcases ha with rfl | rfl <;>
    rcases hb with rfl | rfl <;>
    norm_num [projectorVal]

/-- Fourier-Hadamard sector projector as a 0/1 sign-match test.
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem projectorVal_hadamard_sector_powersum
    {α β a b : Int}
    (hα : α = 1 ∨ α = -1) (hβ : β = 1 ∨ β = -1)
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    ((1 : Int) + α * a + β * b + (α * β) * (a * b)) / 4 =
      if a = α ∧ b = β then 1 else 0 := by
  rcases hα with rfl | rfl <;>
    rcases hβ with rfl | rfl <;>
    rcases ha with rfl | rfl <;>
    rcases hb with rfl | rfl <;>
    norm_num

/-- Paper: complete sign-match characterization for the Fourier-Hadamard projector.
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem paper_projectorVal_sign_match_complete
    {α β a b : Int}
    (hα : α = 1 ∨ α = -1) (hβ : β = 1 ∨ β = -1)
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    projectorVal α β a b = if a = α ∧ b = β then 1 else 0 := by
  rcases hα with rfl | rfl <;>
    rcases hβ with rfl | rfl <;>
    rcases ha with rfl | rfl <;>
    rcases hb with rfl | rfl <;>
    norm_num [projectorVal]

/-- Projector value at matching signs is 1.
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem projectorVal_at_same_signs {α β : Int} (hα : α ^ 2 = 1) (hβ : β ^ 2 = 1) :
    projectorVal α β α β = 1 := by
  have hα1 : α = 1 ∨ α = -1 := by
    have : (α - 1) * (α + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h <;> omega
  have hβ1 : β = 1 ∨ β = -1 := by
    have : (β - 1) * (β + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h <;> omega
  rcases hα1 with rfl | rfl <;> rcases hβ1 with rfl | rfl <;> norm_num [projectorVal]

/-- Projector p_{++}(1,1) = 1 (match corner).
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem projectorVal_at_one_one_one_one :
    projectorVal 1 1 1 1 = 1 := by norm_num [projectorVal]

/-- Projector p_{++}(−1,1) = 0 (mismatch).
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem projectorVal_at_mismatch_zero :
    projectorVal 1 1 (-1) 1 = 0 := by norm_num [projectorVal]

/-- Projector p_{−−}(−1,1) = 1 (match corner).
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem projectorVal_at_neg_one_one_neg_one_one :
    projectorVal (-1) 1 (-1) 1 = 1 := by norm_num [projectorVal]

/-- Projector p_{−−}(−1,−1) = 1 (match corner).
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem projectorVal_at_all_neg_one :
    projectorVal (-1) (-1) (-1) (-1) = 1 := by norm_num [projectorVal]

/-- Paper projectorVal corner table (4 match + 3 mismatch).
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem paper_projectorVal_corner_table :
    projectorVal 1 1 1 1 = 1 ∧
    projectorVal 1 (-1) 1 (-1) = 1 ∧
    projectorVal (-1) 1 (-1) 1 = 1 ∧
    projectorVal (-1) (-1) (-1) (-1) = 1 ∧
    projectorVal 1 1 (-1) 1 = 0 ∧
    projectorVal 1 1 1 (-1) = 0 ∧
    projectorVal 1 1 (-1) (-1) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [projectorVal]

end Omega.EA
