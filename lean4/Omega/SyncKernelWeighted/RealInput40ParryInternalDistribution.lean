import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40Essential20

namespace Omega.SyncKernelWeighted

/-- The four memory-conditioned blocks of the essential `20`-state core. -/
def real_input_40_parry_internal_distribution_block : Fin 4 → Finset ℕ
  | 0 => realInput40Core00
  | 1 => realInput40Core01
  | 2 => realInput40Core10
  | _ => realInput40Core11

/-- The closed-form Parry weights attached to the four memory blocks. -/
def real_input_40_parry_internal_distribution_weight : Fin 4 → ℚ
  | 0 => 1 / 6
  | 1 => 1 / 5
  | 2 => 1 / 5
  | _ => 1 / 4

/-- Conditional Parry weight of an internal synchronization state inside the essential core. -/
def real_input_40_parry_internal_distribution_table (m : Fin 4) (s : ℕ) : ℚ :=
  if s ∈ real_input_40_parry_internal_distribution_block m then
    real_input_40_parry_internal_distribution_weight m
  else
    0

/-- Closed-form table statement for the `20` essential states, organized by the four memory
classes. -/
def real_input_40_parry_internal_distribution_closed_form : Prop :=
  (∀ m : Fin 4,
      ((real_input_40_parry_internal_distribution_block m).card : ℚ) *
          real_input_40_parry_internal_distribution_weight m =
        1) ∧
    ∀ m : Fin 4, ∀ s : ℕ,
      real_input_40_parry_internal_distribution_table m s =
        if s ∈ real_input_40_parry_internal_distribution_block m then
          real_input_40_parry_internal_distribution_weight m
        else
          0

/-- Paper label: `prop:real-input-40-parry-internal-distribution`. The `20` essential states split
into the four audited memory classes of sizes `6/5/5/4`; the closed-form Parry conditional law is
uniform on each class, hence rowwise normalized with weights `1/6`, `1/5`, `1/5`, and `1/4`. -/
theorem paper_real_input_40_parry_internal_distribution :
    real_input_40_parry_internal_distribution_closed_form := by
  constructor
  · intro m
    fin_cases m <;>
      norm_num [real_input_40_parry_internal_distribution_block,
        real_input_40_parry_internal_distribution_weight, realInput40Core00, realInput40Core01,
        realInput40Core10, realInput40Core11]
  · intro m s
    rfl

end Omega.SyncKernelWeighted
