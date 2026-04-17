import Mathlib.Tactic
import Omega.EA.SyncKernelResetWords

namespace Omega.EA

/-- The explicit reset block `00000` used in the regeneration argument. -/
def sync10ResetBlock : List (Fin 3) :=
  [0, 0, 0, 0, 0]

/-- Running the synchronization kernel along concatenated input words is associative. -/
theorem sync10Run_append (q : Sync10State) (left right : List (Fin 3)) :
    sync10Run q (left ++ right) = sync10Run (sync10Run q left) right := by
  induction left generalizing q with
  | nil =>
      simp [sync10Run]
  | cons d left ih =>
      simp [sync10Run, ih]

/-- The block `00000` resets the 10-state synchronization kernel to the state `000`. -/
theorem sync10Run_resetBlock (q : Sync10State) :
    sync10Run q sync10ResetBlock = Sync10State.q000 := by
  cases q <;> native_decide

/-- A `00000` block is a strict regeneration point for the synchronization kernel.
    prop:sync10-regeneration -/
theorem paper_sync10_regeneration
    (q : Sync10State) (pref suffix : List (Fin 3)) :
    sync10Run q (pref ++ sync10ResetBlock ++ suffix) = sync10Run Sync10State.q000 suffix := by
  rw [List.append_assoc, sync10Run_append, sync10Run_append, sync10Run_resetBlock]

end Omega.EA
