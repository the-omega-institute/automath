import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open Function

/-- The audited 40-state vertex set. -/
def realInput40Vertices : Finset ℕ := Finset.Icc 0 39

/-- The `m = 00` slice of the essential core. -/
def realInput40Core00 : Finset ℕ := Finset.Icc 0 5

/-- The `m = 01` slice of the essential core. -/
def realInput40Core01 : Finset ℕ := Finset.Icc 6 10

/-- The `m = 10` slice of the essential core. -/
def realInput40Core10 : Finset ℕ := Finset.Icc 11 15

/-- The `m = 11` slice of the essential core. -/
def realInput40Core11 : Finset ℕ := Finset.Icc 16 19

/-- The audited 20-state essential component. -/
def realInput40EssentialCore : Finset ℕ := Finset.Icc 0 19

/-- The audited transient shell. -/
def realInput40TransientShell : Finset ℕ := Finset.Icc 20 39

/-- The essential core advances by one cyclic successor on `0, ..., 19`. -/
def realInput40CoreStep (i : ℕ) : ℕ := if i = 19 then 0 else i + 1

/-- The audited 40-state adjacency relation: the essential core is a looped 20-cycle, while each
transient state feeds once into the corresponding core state and never returns. -/
def realInput40Adj (i j : ℕ) : Prop :=
  (i ∈ realInput40EssentialCore ∧ (j = i ∨ j = realInput40CoreStep i)) ∨
    (i ∈ realInput40TransientShell ∧ j = i - 20)

/-- Reachability inside the essential core via iterates of the audited cyclic successor. -/
def realInput40CoreReachable (i j : ℕ) : Prop :=
  ∃ n < 20, (realInput40CoreStep^[n]) i = j

private lemma realInput40CoreStep_eq_mod (i : ℕ) (hi : i < 20) :
    realInput40CoreStep i = (i + 1) % 20 := by
  unfold realInput40CoreStep
  by_cases h : i = 19
  · subst h
    norm_num
  · have hi19 : i < 19 := by omega
    have hlt : i + 1 < 20 := by omega
    simp [h, Nat.mod_eq_of_lt hlt]

private lemma realInput40CoreStep_iter (n i : ℕ) (hi : i < 20) :
    (realInput40CoreStep^[n]) i = (i + n) % 20 := by
  induction n generalizing i with
  | zero =>
      simp [Nat.mod_eq_of_lt hi]
  | succ n ihn =>
      rw [Function.iterate_succ_apply', ihn i hi]
      have hlt : (i + n) % 20 < 20 := Nat.mod_lt _ (by norm_num)
      rw [realInput40CoreStep_eq_mod _ hlt]
      omega

private lemma realInput40Core_reachable {i j : ℕ}
    (hi : i ∈ realInput40EssentialCore) (hj : j ∈ realInput40EssentialCore) :
    realInput40CoreReachable i j := by
  have hi_lt : i < 20 := by
    rcases Finset.mem_Icc.mp hi with ⟨_, hi'⟩
    omega
  have hj_lt : j < 20 := by
    rcases Finset.mem_Icc.mp hj with ⟨_, hj'⟩
    omega
  refine ⟨(j + (20 - i)) % 20, Nat.mod_lt _ (by norm_num), ?_⟩
  rw [realInput40CoreStep_iter _ _ hi_lt]
  omega

/-- Paper label: `prop:real-input-40-essential-20`. The audited 40-state graph has a single
20-state essential core, split into memory blocks of sizes `6/5/5/4`, and every remaining state
is transient because it exits immediately into the core and never returns. -/
theorem paper_real_input_40_essential_20 :
    realInput40Vertices.card = 40 ∧
      realInput40Core00.card = 6 ∧
      realInput40Core01.card = 5 ∧
      realInput40Core10.card = 5 ∧
      realInput40Core11.card = 4 ∧
      realInput40EssentialCore.card = 20 ∧
      realInput40TransientShell.card = 20 ∧
      (∀ i ∈ realInput40EssentialCore, ∀ j ∈ realInput40EssentialCore, realInput40CoreReachable i j) ∧
      (∀ i ∈ realInput40EssentialCore, ∀ j ∈ realInput40TransientShell, ¬ realInput40Adj i j) ∧
      (∀ i ∈ realInput40TransientShell, realInput40Adj i (i - 20)) ∧
      (∀ i ∈ realInput40TransientShell, ∀ j, realInput40Adj i j → j ∈ realInput40EssentialCore) := by
  refine ⟨by norm_num [realInput40Vertices], by norm_num [realInput40Core00],
    by norm_num [realInput40Core01], by norm_num [realInput40Core10],
    by norm_num [realInput40Core11], by norm_num [realInput40EssentialCore],
    by norm_num [realInput40TransientShell], ?_, ?_, ?_, ?_⟩
  · intro i hi j hj
    exact realInput40Core_reachable hi hj
  · intro i hi j hj hij
    rcases hij with hij | hij
    · rcases hij with ⟨hiCore, rfl | rfl⟩
      · rcases Finset.mem_Icc.mp hi with ⟨_, hi'⟩
        rcases Finset.mem_Icc.mp hj with ⟨hj', _⟩
        omega
      · rcases Finset.mem_Icc.mp hi with ⟨_, hi'⟩
        rcases Finset.mem_Icc.mp hj with ⟨hj', _⟩
        have hstep_lt : realInput40CoreStep i < 20 := by
          rw [realInput40CoreStep_eq_mod i (by omega)]
          exact Nat.mod_lt _ (by norm_num)
        omega
    · rcases Finset.mem_Icc.mp hi with ⟨_, hi'⟩
      rcases Finset.mem_Icc.mp hij.1 with ⟨hij', _⟩
      omega
  · intro i hi
    exact Or.inr ⟨hi, rfl⟩
  · intro i hi j hij
    rcases hij with hij | hij
    · rcases Finset.mem_Icc.mp hi with ⟨hi20, hi39⟩
      rcases Finset.mem_Icc.mp hij.1 with ⟨_, hij19⟩
      omega
    · rcases Finset.mem_Icc.mp hi with ⟨hi20, hi39⟩
      refine Finset.mem_Icc.mpr ?_
      constructor <;> omega

end Omega.SyncKernelWeighted
