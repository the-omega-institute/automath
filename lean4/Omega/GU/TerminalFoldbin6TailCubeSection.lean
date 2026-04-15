import Mathlib.Tactic
import Omega.GU.ZeckendorfCountClosure

namespace Omega.GU

/-- The three tail bits appearing in the window-6 `6+3` decomposition. -/
structure TailBits where
  c7 : Bool
  c8 : Bool
  c9 : Bool

/-- Convert a Boolean tail bit to its `0/1` arithmetic value. -/
def boolBit (b : Bool) : Nat :=
  cond b 1 0

/-- The specialized value `K(6) = 9`. -/
def terminalFoldbin6K : Nat := 9

/-- The tail offset associated with a choice of `(c₇,c₈,c₉)`. -/
def terminalFoldbin6TailOffset (t : TailBits) : Nat :=
  21 * boolBit t.c7 + 34 * boolBit t.c8 + 55 * boolBit t.c9

/-- The feasible tail-cube section from the paper statement. -/
def terminalFoldbin6Feasible (w6 baseValue : Nat) (t : TailBits) : Prop :=
  boolBit t.c7 * boolBit t.c8 = 0 ∧
  boolBit t.c8 * boolBit t.c9 = 0 ∧
  w6 * boolBit t.c7 = 0 ∧
  baseValue + terminalFoldbin6TailOffset t ≤ 63

/-- Paper-facing wrapper for the window-6 tail cube section:
    `K(6)=9`, the three tail weights are `(21,34,55)`, the forbidden vertex `(1,0,1)` is
    globally infeasible, and every feasible tail offset lies in `{0,21,34,55}`.
    prop:terminal-foldbin6-tail-cube-section -/
theorem paper_terminal_foldbin6_tail_cube_section (w6 baseValue : Nat) :
    terminalFoldbin6K = 9 ∧
    terminalFoldbin6TailOffset ⟨true, false, false⟩ = Nat.fib 8 ∧
    terminalFoldbin6TailOffset ⟨false, true, false⟩ = Nat.fib 9 ∧
    terminalFoldbin6TailOffset ⟨false, false, true⟩ = Nat.fib 10 ∧
    ¬ terminalFoldbin6Feasible 0 0 ⟨true, false, true⟩ ∧
    (∀ t : TailBits,
      terminalFoldbin6Feasible w6 baseValue t →
        terminalFoldbin6TailOffset t ∈ ({0, 21, 34, 55} : Finset Nat)) := by
  rcases fold6_tail_offsets with ⟨h8, h9, h10⟩
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [terminalFoldbin6TailOffset, boolBit, h8]
  · simp [terminalFoldbin6TailOffset, boolBit, h9]
  · simp [terminalFoldbin6TailOffset, boolBit, h10]
  · simp [terminalFoldbin6Feasible, terminalFoldbin6TailOffset, boolBit]
  · rintro ⟨c7, c8, c9⟩ h
    cases c7 <;> cases c8 <;> cases c9 <;>
      simp [terminalFoldbin6Feasible, terminalFoldbin6TailOffset, boolBit] at h ⊢

end Omega.GU
