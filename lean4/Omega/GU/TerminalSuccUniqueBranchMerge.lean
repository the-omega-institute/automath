import Mathlib.Tactic
import Omega.Folding.FiberArithmeticProperties
import Omega.Folding.Window6
import Omega.GU.ZeckendorfCountClosure

namespace Omega.GU

open Omega.X

noncomputable section

/-- The unique window-6 branching word `101010`. -/
def terminalSuccBranchPoint6 : X 6 := X.ofNat 6 12

/-- The unique window-6 reset/merge word `000000`. -/
def terminalSuccMergePoint6 : X 6 := X.ofNat 6 0

/-- The non-reset branch image `000001`. -/
def terminalSuccCarryPoint6 : X 6 := X.ofNat 6 13

/-- The top predecessor `010101` of the reset word. -/
def terminalSuccTopPoint6 : X 6 := X.ofNat 6 20

/-- The window-6 terminal successor audit: everything follows the cyclic successor except the
alternating boundary word `101010`, which branches to both `000000` and `000001`. -/
def terminalSucc6 (w : X 6) : Finset (X 6) :=
  if w = terminalSuccBranchPoint6 then
    {terminalSuccMergePoint6, terminalSuccCarryPoint6}
  else
    {X.ofNat 6 ((stableValue w + 1) % Nat.fib 8)}

/-- The corresponding predecessor audit: only `000000` has two predecessors, namely `010101` and
`101010`; every other node has the unique predecessor obtained by subtracting one modulo `21`. -/
def terminalPred6 (w : X 6) : Finset (X 6) :=
  if w = terminalSuccMergePoint6 then
    {terminalSuccTopPoint6, terminalSuccBranchPoint6}
  else
    {X.ofNat 6 ((stableValue w + Nat.fib 8 - 1) % Nat.fib 8)}

private lemma fib8_eq_twentyone : Nat.fib 8 = 21 := fold6_tail_offsets.1

private lemma branchpoint_ne_carrypoint :
    terminalSuccBranchPoint6 ≠ terminalSuccCarryPoint6 := by
  simpa [terminalSuccBranchPoint6, terminalSuccCarryPoint6] using succ_branch_at_b6

private lemma mergepoint_ne_carrypoint :
    terminalSuccMergePoint6 ≠ terminalSuccCarryPoint6 := by
  intro h
  have hval := congrArg stableValue h
  have h13 : stableValue (terminalSuccCarryPoint6) = 13 := by
    rw [terminalSuccCarryPoint6, stableValue_ofNat_lt 13]
    rw [fib8_eq_twentyone]
    omega
  simp [terminalSuccMergePoint6, zero_is_merge_point, h13] at hval

private lemma toppoint_ne_branchpoint :
    terminalSuccTopPoint6 ≠ terminalSuccBranchPoint6 := by
  intro h
  have hval := congrArg stableValue h
  have h20 : stableValue terminalSuccTopPoint6 = 20 := by
    rw [terminalSuccTopPoint6, stableValue_ofNat_lt 20]
    rw [fib8_eq_twentyone]
    omega
  have h12 : stableValue terminalSuccBranchPoint6 = 12 := by
    rw [terminalSuccBranchPoint6, stableValue_ofNat_lt 12]
    rw [fib8_eq_twentyone]
    omega
  simp [h20, h12] at hval

theorem paper_terminal_succ_unique_branch_merge :
    (∀ w : X 6, (terminalSucc6 w).card = 2 ↔ w = terminalSuccBranchPoint6) ∧
      (terminalSucc6 terminalSuccBranchPoint6 = {terminalSuccMergePoint6, terminalSuccCarryPoint6} ∧
        terminalPred6 terminalSuccMergePoint6 = {terminalSuccTopPoint6, terminalSuccBranchPoint6}) ∧
      (∀ w : X 6, (terminalPred6 w).card = 2 ↔ w = terminalSuccMergePoint6) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w
    by_cases hw : w = terminalSuccBranchPoint6
    · subst hw
      simp [terminalSucc6, mergepoint_ne_carrypoint]
    · simp [terminalSucc6, hw]
  · refine ⟨?_, ?_⟩
    · simp [terminalSucc6]
    · simp [terminalPred6]
  · intro w
    by_cases hw : w = terminalSuccMergePoint6
    · subst hw
      simp [terminalPred6, toppoint_ne_branchpoint]
    · simp [terminalPred6, hw]

end

end Omega.GU
