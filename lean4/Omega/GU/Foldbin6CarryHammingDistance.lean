import Mathlib.Tactic

namespace Omega.GU

/-- The length of the carry chain triggered by adding `2` at bit `1`, measured by the initial run
of `1` bits in positions `1,2,3,4`. -/
def foldbin6CarryRunLength (V : Nat) : Nat :=
  if V % 4 < 2 then 0
  else if V % 8 < 6 then 1
  else if V % 16 < 14 then 2
  else if V % 32 < 30 then 3
  else 4

/-- The Hamming distance between the binary expansions of `V` and `V + 34`. -/
def foldbin6CarryHammingDistance (V : Nat) : Nat :=
  if V % 4 < 2 then 2
  else if V % 8 < 6 then 3
  else if V % 16 < 14 then 4
  else if V % 32 < 30 then 5
  else 6

/-- Paper label: `thm:foldbin6-carry-hamming-distance`. Since `34 = 2^5 + 2`, the addition flips
the `2^5` bit and exactly the carry chain started at bit `1`. -/
theorem paper_foldbin6_carry_hamming_distance (V : Nat) (hV : V < 32) :
    foldbin6CarryHammingDistance V = 2 + foldbin6CarryRunLength V := by
  unfold foldbin6CarryHammingDistance foldbin6CarryRunLength
  interval_cases V <;> native_decide

end Omega.GU
