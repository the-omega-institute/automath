import Mathlib.Tactic

namespace Omega.EA

/-- The ten states of the synchronization kernel, in the appendix order
`000,001,002,010,100,101,0-12,1-12,01-1,11-1`. -/
inductive Sync10State
  | q000 | q001 | q002 | q010 | q100 | q101 | q0m12 | q1m12 | q01m1 | q11m1
  deriving DecidableEq, Fintype, Repr

/-- The deterministic transition table of the 10-state synchronization kernel. -/
def sync10Step : Sync10State → Fin 3 → Sync10State
  | .q000, ⟨0, _⟩ => .q000
  | .q000, ⟨1, _⟩ => .q001
  | .q000, ⟨2, _⟩ => .q002
  | .q100, ⟨0, _⟩ => .q000
  | .q100, ⟨1, _⟩ => .q001
  | .q100, ⟨2, _⟩ => .q002
  | .q001, ⟨0, _⟩ => .q010
  | .q001, ⟨1, _⟩ => .q100
  | .q001, ⟨2, _⟩ => .q101
  | .q002, ⟨0, _⟩ => .q11m1
  | .q002, ⟨1, _⟩ => .q000
  | .q002, ⟨2, _⟩ => .q001
  | .q010, ⟨0, _⟩ => .q100
  | .q010, ⟨1, _⟩ => .q101
  | .q010, ⟨2, _⟩ => .q0m12
  | .q101, ⟨0, _⟩ => .q010
  | .q101, ⟨1, _⟩ => .q100
  | .q101, ⟨2, _⟩ => .q101
  | .q0m12, ⟨0, _⟩ => .q01m1
  | .q0m12, ⟨1, _⟩ => .q010
  | .q0m12, ⟨2, _⟩ => .q100
  | .q1m12, ⟨0, _⟩ => .q01m1
  | .q1m12, ⟨1, _⟩ => .q010
  | .q1m12, ⟨2, _⟩ => .q100
  | .q01m1, ⟨0, _⟩ => .q001
  | .q01m1, ⟨1, _⟩ => .q002
  | .q01m1, ⟨2, _⟩ => .q1m12
  | .q11m1, ⟨0, _⟩ => .q001
  | .q11m1, ⟨1, _⟩ => .q002
  | .q11m1, ⟨2, _⟩ => .q1m12

/-- Run the synchronization kernel on a finite input word. -/
def sync10Run : Sync10State → List (Fin 3) → Sync10State
  | q, [] => q
  | q, d :: w => sync10Run (sync10Step q d) w

/-- Run the synchronization kernel on a fixed-length word. -/
def sync10RunWord (q : Sync10State) (w : Fin n → Fin 3) : Sync10State :=
  sync10Run q (List.ofFn w)

/-- A reset word of length `n` for the 10-state synchronization kernel. -/
def sync10HasResetWordOfLength (n : Nat) : Prop :=
  ∃ w : Fin n → Fin 3, ∀ q : Sync10State, sync10RunWord q w = sync10RunWord Sync10State.q000 w

/-- A reset word of length strictly less than `n`. -/
def sync10HasResetWordOfLengthLessThan (n : Nat) : Prop :=
  ∃ k < n, sync10HasResetWordOfLength k

instance instDecidableSync10HasResetWordOfLength (n : Nat) :
    Decidable (sync10HasResetWordOfLength n) := by
  unfold sync10HasResetWordOfLength sync10RunWord
  infer_instance

instance instDecidableSync10HasResetWordOfLengthLessThan (n : Nat) :
    Decidable (sync10HasResetWordOfLengthLessThan n) := by
  unfold sync10HasResetWordOfLengthLessThan
  infer_instance

private def zeroDigit : Fin 3 := ⟨0, by decide⟩

private def zeroWord5 : Fin 5 → Fin 3 := fun _ => zeroDigit

/-- The explicit word `00000` resets the kernel to state `000`. -/
theorem sync10_reset_00000 :
    ∀ q : Sync10State, sync10RunWord q zeroWord5 = Sync10State.q000 := by
  native_decide

/-- The 10-state synchronization kernel has shortest reset length exactly `5`.
    prop:sync10-reset-length-5 -/
theorem paper_sync10_reset_length_5 :
    sync10HasResetWordOfLength 5 ∧ ¬ sync10HasResetWordOfLengthLessThan 5 := by
  constructor
  · refine ⟨zeroWord5, ?_⟩
    intro q
    rw [sync10_reset_00000 q, sync10_reset_00000 Sync10State.q000]
  · native_decide

end Omega.EA
