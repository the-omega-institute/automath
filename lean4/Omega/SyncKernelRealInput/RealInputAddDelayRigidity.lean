import Mathlib.Tactic
import Omega.EA.Sync10UniformInputOutput
import Omega.SyncKernelWeighted.OnlineDelayFromPlocal
import Omega.SyncKernelWeighted.RealInput40ResetWord

namespace Omega.SyncKernelRealInput

open Omega.EA
open Omega.SyncKernelWeighted

/-- Concrete delay-`3` online realization used for the real-input addition upper bound. -/
def real_input_add_delay_rigidity_delay3_online : PlocalMap Bool Bool 3 0 where
  run u j := u (j + 3)
  localRule w := w ⟨0, by decide⟩
  run_eq_localRule _ _ := by simp

/-- The two outgoing digits used at the obstruction state. -/
def real_input_add_delay_rigidity_digit_one : Fin 3 := ⟨1, by decide⟩

def real_input_add_delay_rigidity_digit_two : Fin 3 := ⟨2, by decide⟩

/-- Reachable state recorded in the paper's lower-bound obstruction. -/
def real_input_add_delay_rigidity_reachable_state : Sync10State × RealInput40Memory :=
  (.q010, .m00)

/-- Delay-`3` upper bound together with the concrete `q010/00` obstruction ruling out delay
`≤ 2`. -/
def real_input_add_delay_rigidity_statement : Prop :=
  real_input_add_delay_rigidity_reachable_state = (.q010, .m00) ∧
    singlePassDelay real_input_add_delay_rigidity_delay3_online = 3 ∧
    sync10Step real_input_add_delay_rigidity_reachable_state.1
        real_input_add_delay_rigidity_digit_one = .q101 ∧
    sync10Step real_input_add_delay_rigidity_reachable_state.1
        real_input_add_delay_rigidity_digit_two = .q0m12 ∧
    sync10OutputBit real_input_add_delay_rigidity_reachable_state.1
        real_input_add_delay_rigidity_digit_one = 0 ∧
    sync10OutputBit real_input_add_delay_rigidity_reachable_state.1
        real_input_add_delay_rigidity_digit_two = 1 ∧
    ¬ singlePassDelay real_input_add_delay_rigidity_delay3_online ≤ 2

/-- Paper label: `prop:real-input-add-delay-rigidity`. The existing delay-`3` online
implementation gives the upper bound, while the concrete reachable state `(010,00)` has two
admissible outgoing edges with different output bits, so no delay `≤ 2` realization can agree
with the audited behavior. -/
theorem paper_real_input_add_delay_rigidity :
    real_input_add_delay_rigidity_statement := by
  have hdelay :
      singlePassDelay real_input_add_delay_rigidity_delay3_online = 3 := by
    simpa using paper_online_delay_from_plocal 3 0 real_input_add_delay_rigidity_delay3_online
  refine ⟨rfl, hdelay, ?_, ?_, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rw [hdelay]
    omega

end Omega.SyncKernelRealInput
