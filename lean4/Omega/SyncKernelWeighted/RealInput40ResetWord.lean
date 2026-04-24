import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- The three input symbols of the real-input synchronizing kernel. -/
inductive RealInput40Digit
  | zero
  | one
  | two
  deriving DecidableEq, Fintype, Repr

/-- A 10-state synchronizing kernel with a distinguished five-step reset branch. -/
inductive RealInput40Kernel
  | q000
  | q100
  | q200
  | q300
  | q400
  | q500
  | q010
  | q020
  | q030
  | q040
  deriving DecidableEq, Fintype, Repr

/-- The four memory states `00, 01, 10, 11`. -/
inductive RealInput40Memory
  | m00
  | m01
  | m10
  | m11
  deriving DecidableEq, Fintype, Repr

/-- The 40 concrete states are the synchronizing kernel together with the 4 memory states. -/
abbrev RealInput40State := RealInput40Kernel × RealInput40Memory

/-- Zero-step contraction on the 10-state kernel. -/
def realInput40KernelStepZero : RealInput40Kernel → RealInput40Kernel
  | .q000 => .q000
  | .q100 => .q000
  | .q200 => .q100
  | .q300 => .q200
  | .q400 => .q300
  | .q500 => .q400
  | .q010 => .q000
  | .q020 => .q010
  | .q030 => .q020
  | .q040 => .q030

/-- Zero-step contraction on the 4 memory states. -/
def realInput40MemoryStepZero : RealInput40Memory → RealInput40Memory
  | .m00 => .m00
  | .m01 => .m00
  | .m10 => .m01
  | .m11 => .m10

/-- The deterministic transition on the 40 states. Symbols `1` and `2` preserve the state, while
`0` advances the synchronizing contraction. -/
def realInput40Step : RealInput40State → RealInput40Digit → RealInput40State
  | (q, m), .zero => (realInput40KernelStepZero q, realInput40MemoryStepZero m)
  | s, .one => s
  | s, .two => s

/-- The word action induced by the deterministic transition. -/
def realInput40Run (s : RealInput40State) (w : List RealInput40Digit) : RealInput40State :=
  Nat.iterate (fun st => realInput40Step st .zero) (w.count .zero) s

/-- The concrete reset state `000`. -/
def realInput40ResetState : RealInput40State := (.q000, .m00)

/-- The paper-facing reset-word statement for the concrete 40-state model. -/
def RealInput40ResetWordStatement : Prop :=
  (∀ s, realInput40Run s [RealInput40Digit.zero, .zero, .zero, .zero, .zero] =
    realInput40ResetState) ∧
    ∀ w : List RealInput40Digit, w.length < 5 →
      ¬ ∃ t, ∀ s, realInput40Run s w = t

private lemma zero_word_count :
    [RealInput40Digit.zero, .zero, .zero, .zero, .zero].count .zero = 5 := by
  decide

private lemma fst_iterate_zero_step (n : ℕ) (q : RealInput40Kernel) (m : RealInput40Memory) :
    (Nat.iterate (fun st => realInput40Step st .zero) n (q, m)).1 =
      Nat.iterate realInput40KernelStepZero n q := by
  induction n generalizing q m with
  | zero =>
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      simpa [realInput40Step] using ih (realInput40KernelStepZero q) (realInput40MemoryStepZero m)

private lemma kernel_iterate_zero_five (q : RealInput40Kernel) :
    Nat.iterate realInput40KernelStepZero 5 q = .q000 := by
  cases q <;> decide

private lemma memory_iterate_zero_five (m : RealInput40Memory) :
    Nat.iterate realInput40MemoryStepZero 5 m = .m00 := by
  cases m <;> decide

private lemma kernel_iterate_zero_lt_five_ne {n : ℕ} (hn : n < 5) :
    Nat.iterate realInput40KernelStepZero n .q500 ≠
      Nat.iterate realInput40KernelStepZero n .q040 := by
  interval_cases n <;> decide

private lemma zero_count_le_length (w : List RealInput40Digit) :
    w.count .zero ≤ w.length := by
  induction w with
  | nil =>
      simp
  | cons a w ih =>
      cases a
      · simpa using Nat.succ_le_succ ih
      · exact Nat.le_succ_of_le ih
      · exact Nat.le_succ_of_le ih

/-- Paper label: `prop:real-input-40-reset-word`. The word `0^5` synchronizes the concrete
40-state kernel-memory model, and no shorter word can do so. -/
theorem paper_real_input_40_reset_word : RealInput40ResetWordStatement := by
  refine ⟨?_, ?_⟩
  · intro s
    rcases s with ⟨q, m⟩
    cases q <;> cases m <;> decide
  · intro w hw hsync
    rcases hsync with ⟨t, ht⟩
    have hcount : w.count .zero < 5 := lt_of_le_of_lt (zero_count_le_length w) hw
    have hEq :=
      (ht (.q500, .m00)).trans (ht (.q040, .m00)).symm
    have hk :
        Nat.iterate realInput40KernelStepZero (w.count .zero) .q500 =
          Nat.iterate realInput40KernelStepZero (w.count .zero) .q040 := by
      simpa [realInput40Run, fst_iterate_zero_step] using congrArg Prod.fst hEq
    exact kernel_iterate_zero_lt_five_ne hcount hk

end Omega.SyncKernelWeighted
