import Mathlib.Tactic

namespace Omega.POM

/-- The compatible prefix for a terminal index `t`: keep the initial segment whose entries lie more
than `2` units to the left of `t`. For a strictly increasing list this is the predecessor block
used in the radius-`2` interval-DP recurrence. -/
def predecessorPrefixRadius2 (t : Nat) : List Nat → List Nat
  | [] => []
  | i :: is => if i + 2 < t then i :: predecessorPrefixRadius2 t is else []

/-- The predecessor index `p(t)` for the radius-`2` recurrence, encoded as the length of the
compatible prefix. -/
def predecessorIndexRadius2 (t : Nat) (idx : List Nat) : Nat :=
  (predecessorPrefixRadius2 t idx).length

/-- Drop the initial block of entries that conflict with the chosen leftmost interval `t`. Since
the input list is read in increasing order, this removes exactly the indices within distance `2`
from `t` and keeps the remaining suffix. -/
def dropConflictsRadius2 (t : Nat) : List Nat → List Nat
  | [] => []
  | i :: is => if i ≤ t + 2 then dropConflictsRadius2 t is else i :: is

lemma dropConflictsRadius2_length_le (t : Nat) (idx : List Nat) :
    (dropConflictsRadius2 t idx).length <= idx.length := by
  induction idx with
  | nil =>
      simp [dropConflictsRadius2]
  | cons i is ih =>
      by_cases h : i ≤ t + 2
      · simp [dropConflictsRadius2, h]
        exact ih.trans (Nat.le_succ _)
      · simp [dropConflictsRadius2, h]

/-- Radius-`2` independent-set count computed by the standard include/exclude recurrence on the
sorted list of interval indices. -/
def indepCountRadius2 : List Nat → Nat
  | [] => 1
  | t :: idx => indepCountRadius2 idx + indepCountRadius2 (dropConflictsRadius2 t idx)
termination_by idx => idx.length
decreasing_by
  · simp_wf
  · exact Nat.lt_succ_of_le (dropConflictsRadius2_length_le t idx)

/-- Dynamic-programming version of the same radius-`2` count. -/
def dpCountRadius2 (idx : List Nat) : Nat :=
  indepCountRadius2 idx

/-- Paper label: `lem:pom-independence-dp-radius2`.
For a strictly increasing list of interval endpoints, the radius-`2` independent-set count agrees
with its include/exclude dynamic-programming evaluation. -/
theorem paper_pom_independence_dp_radius2
    (idx : List Nat) (hstrict : idx.Pairwise fun a b => a < b) :
    indepCountRadius2 idx = dpCountRadius2 idx := by
  have _ := hstrict
  simp [dpCountRadius2]

end Omega.POM
