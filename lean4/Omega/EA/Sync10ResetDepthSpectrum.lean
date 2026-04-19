import Mathlib.Tactic
import Omega.EA.Sync10Regeneration

namespace Omega.EA

/-- A word of length `n` that resets the synchronization kernel to the target state `t`. -/
def sync10ResetsToTargetOfLength (t : Sync10State) (n : Nat) : Prop :=
  ∃ w : Fin n → Fin 3, ∀ q : Sync10State, sync10RunWord q w = t

/-- A reset word to the target state `t` of length strictly less than `n`. -/
def sync10ResetsToTargetOfLengthLessThan (t : Sync10State) (n : Nat) : Prop :=
  ∃ k < n, sync10ResetsToTargetOfLength t k

instance instDecidableSync10ResetsToTargetOfLength (t : Sync10State) (n : Nat) :
    Decidable (sync10ResetsToTargetOfLength t n) := by
  unfold sync10ResetsToTargetOfLength sync10RunWord
  infer_instance

instance instDecidableSync10ResetsToTargetOfLengthLessThan (t : Sync10State) (n : Nat) :
    Decidable (sync10ResetsToTargetOfLengthLessThan t n) := by
  unfold sync10ResetsToTargetOfLengthLessThan
  infer_instance

private def d0 : Fin 3 := ⟨0, by decide⟩
private def d1 : Fin 3 := ⟨1, by decide⟩
private def d2 : Fin 3 := ⟨2, by decide⟩

private def word00000 : Fin 5 → Fin 3 := ![d0, d0, d0, d0, d0]
private def word00001 : Fin 5 → Fin 3 := ![d0, d0, d0, d0, d1]
private def word00002 : Fin 5 → Fin 3 := ![d0, d0, d0, d0, d2]
private def word00010 : Fin 5 → Fin 3 := ![d0, d0, d0, d1, d0]
private def word00011 : Fin 5 → Fin 3 := ![d0, d0, d0, d1, d1]
private def word00012 : Fin 5 → Fin 3 := ![d0, d0, d0, d1, d2]
private def word10202 : Fin 5 → Fin 3 := ![d1, d0, d2, d0, d2]
private def word02020 : Fin 5 → Fin 3 := ![d0, d2, d0, d2, d0]
private def word000102 : Fin 6 → Fin 3 := ![d0, d0, d0, d1, d0, d2]
private def word000020 : Fin 6 → Fin 3 := ![d0, d0, d0, d0, d2, d0]

private theorem word00000_resets :
    ∀ q : Sync10State, sync10RunWord q word00000 = Sync10State.q000 := by
  native_decide

private theorem word00001_resets :
    ∀ q : Sync10State, sync10RunWord q word00001 = Sync10State.q001 := by
  native_decide

private theorem word00002_resets :
    ∀ q : Sync10State, sync10RunWord q word00002 = Sync10State.q002 := by
  native_decide

private theorem word00010_resets :
    ∀ q : Sync10State, sync10RunWord q word00010 = Sync10State.q010 := by
  native_decide

private theorem word00011_resets :
    ∀ q : Sync10State, sync10RunWord q word00011 = Sync10State.q100 := by
  native_decide

private theorem word00012_resets :
    ∀ q : Sync10State, sync10RunWord q word00012 = Sync10State.q101 := by
  native_decide

private theorem word10202_resets :
    ∀ q : Sync10State, sync10RunWord q word10202 = Sync10State.q1m12 := by
  native_decide

private theorem word02020_resets :
    ∀ q : Sync10State, sync10RunWord q word02020 = Sync10State.q01m1 := by
  native_decide

private theorem word000102_resets :
    ∀ q : Sync10State, sync10RunWord q word000102 = Sync10State.q0m12 := by
  native_decide

private theorem word000020_resets :
    ∀ q : Sync10State, sync10RunWord q word000020 = Sync10State.q11m1 := by
  native_decide

private theorem reset_q000_len5 :
    sync10ResetsToTargetOfLength Sync10State.q000 5 := by
  exact ⟨word00000, word00000_resets⟩

private theorem reset_q001_len5 :
    sync10ResetsToTargetOfLength Sync10State.q001 5 := by
  exact ⟨word00001, word00001_resets⟩

private theorem reset_q002_len5 :
    sync10ResetsToTargetOfLength Sync10State.q002 5 := by
  exact ⟨word00002, word00002_resets⟩

private theorem reset_q010_len5 :
    sync10ResetsToTargetOfLength Sync10State.q010 5 := by
  exact ⟨word00010, word00010_resets⟩

private theorem reset_q100_len5 :
    sync10ResetsToTargetOfLength Sync10State.q100 5 := by
  exact ⟨word00011, word00011_resets⟩

private theorem reset_q101_len5 :
    sync10ResetsToTargetOfLength Sync10State.q101 5 := by
  exact ⟨word00012, word00012_resets⟩

private theorem reset_q1m12_len5 :
    sync10ResetsToTargetOfLength Sync10State.q1m12 5 := by
  exact ⟨word10202, word10202_resets⟩

private theorem reset_q01m1_len5 :
    sync10ResetsToTargetOfLength Sync10State.q01m1 5 := by
  exact ⟨word02020, word02020_resets⟩

private theorem reset_q0m12_len6 :
    sync10ResetsToTargetOfLength Sync10State.q0m12 6 := by
  exact ⟨word000102, word000102_resets⟩

private theorem reset_q11m1_len6 :
    sync10ResetsToTargetOfLength Sync10State.q11m1 6 := by
  exact ⟨word000020, word000020_resets⟩

/-- The least target reset depth found by exhaustive search up to length `6`. -/
def sync10ResetDepth (t : Sync10State) : Nat :=
  if sync10ResetsToTargetOfLength t 0 then 0 else
  if sync10ResetsToTargetOfLength t 1 then 1 else
  if sync10ResetsToTargetOfLength t 2 then 2 else
  if sync10ResetsToTargetOfLength t 3 then 3 else
  if sync10ResetsToTargetOfLength t 4 then 4 else
  if sync10ResetsToTargetOfLength t 5 then 5 else
  if sync10ResetsToTargetOfLength t 6 then 6 else 7

private theorem depth_q000 : sync10ResetDepth Sync10State.q000 = 5 := by
  native_decide

private theorem depth_q001 : sync10ResetDepth Sync10State.q001 = 5 := by
  native_decide

private theorem depth_q002 : sync10ResetDepth Sync10State.q002 = 5 := by
  native_decide

private theorem depth_q010 : sync10ResetDepth Sync10State.q010 = 5 := by
  native_decide

private theorem depth_q100 : sync10ResetDepth Sync10State.q100 = 5 := by
  native_decide

private theorem depth_q101 : sync10ResetDepth Sync10State.q101 = 5 := by
  native_decide

private theorem depth_q0m12 : sync10ResetDepth Sync10State.q0m12 = 6 := by
  native_decide

private theorem depth_q1m12 : sync10ResetDepth Sync10State.q1m12 = 5 := by
  native_decide

private theorem depth_q01m1 : sync10ResetDepth Sync10State.q01m1 = 5 := by
  native_decide

private theorem depth_q11m1 : sync10ResetDepth Sync10State.q11m1 = 6 := by
  native_decide

private theorem depth_exceptional_targets :
    (Finset.univ.filter fun t : Sync10State => sync10ResetDepth t = 6) =
      {Sync10State.q0m12, Sync10State.q11m1} := by
  native_decide

/-- The reset-depth spectrum of the 10-state synchronization kernel is concentrated at depths `5`
and `6`: exactly the two target states `0-12` and `11-1` first appear at depth `6`, while the
other eight target states already admit depth-`5` reset words.
    prop:sync10-reset-depth-spectrum -/
theorem paper_sync10_reset_depth_spectrum :
    sync10ResetDepth Sync10State.q000 = 5 ∧
      sync10ResetDepth Sync10State.q001 = 5 ∧
      sync10ResetDepth Sync10State.q002 = 5 ∧
      sync10ResetDepth Sync10State.q010 = 5 ∧
      sync10ResetDepth Sync10State.q100 = 5 ∧
      sync10ResetDepth Sync10State.q101 = 5 ∧
      sync10ResetDepth Sync10State.q0m12 = 6 ∧
      sync10ResetDepth Sync10State.q1m12 = 5 ∧
      sync10ResetDepth Sync10State.q01m1 = 5 ∧
      sync10ResetDepth Sync10State.q11m1 = 6 ∧
      (Finset.univ.filter fun t : Sync10State => sync10ResetDepth t = 6) =
        {Sync10State.q0m12, Sync10State.q11m1} := by
  exact ⟨depth_q000, depth_q001, depth_q002, depth_q010, depth_q100, depth_q101, depth_q0m12,
    depth_q1m12, depth_q01m1, depth_q11m1, depth_exceptional_targets⟩

end Omega.EA
