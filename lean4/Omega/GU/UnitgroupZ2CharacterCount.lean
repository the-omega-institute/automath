import Omega.Folding.ZeckendorfSignature
import Mathlib.Data.ZMod.Basic

namespace Omega.GU.UnitgroupZ2CharacterCount

open Finset

/--
Counting nontrivial involutive classes for the `m = 5, 6` unit-group interfaces.
For the paper proposition `prop:unitgroup-z2-character-count-m5-m6`, these counts
are the finite combinatorial proxy for the number of nontrivial `ℤ₂`-characters.
-/
def involutionCount (n : ℕ) [NeZero n] : ℕ :=
  (Finset.univ.filter (fun x : ZMod n => x * x = 1)).card - 1

theorem involutionCount_13 : involutionCount 13 = 1 := by
  simpa [involutionCount] using Omega.ZeckSig.zmod13_sq_eq_one_count

theorem involutionCount_21 : involutionCount 21 = 3 := by
  simpa [involutionCount] using Omega.ZeckSig.zmod21_sq_eq_one_count

/--
Paper-facing seed theorem for `prop:unitgroup-z2-character-count-m5-m6`.
-/
theorem paper_unitgroup_z2_character_count_m5_m6_seeds :
    involutionCount 13 = 1 ∧ involutionCount 21 = 3 := by
  exact ⟨involutionCount_13, involutionCount_21⟩

/--
Wrapper theorem matching the paper-facing package name.
-/
theorem paper_unitgroup_z2_character_count_m5_m6_package :
    involutionCount 13 = 1 ∧ involutionCount 21 = 3 := by
  exact paper_unitgroup_z2_character_count_m5_m6_seeds

/--
Paper-facing proposition `prop:unitgroup-z2-character-count-m5-m6`.
-/
theorem paper_unitgroup_z2_character_count_m5_m6 :
    involutionCount 13 = 1 ∧ involutionCount 21 = 3 := by
  exact ⟨involutionCount_13, involutionCount_21⟩

end Omega.GU.UnitgroupZ2CharacterCount
