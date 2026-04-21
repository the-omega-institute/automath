import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic
import Omega.Folding.FiberGaugeVolumeDoublingV2DigitSum

namespace Omega.Conclusion

open scoped BigOperators

private lemma basePDigitSum_two_one_le {n : ℕ} (hn : 0 < n) :
    1 ≤ Omega.Folding.basePDigitSum 2 n := by
  rw [Omega.Folding.basePDigitSum]
  have hnil : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (Nat.ne_of_gt hn)
  exact Nat.sum_pos_iff_exists_pos.mpr
    ⟨_, List.getLast_mem hnil, Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero 2 (Nat.ne_of_gt hn))⟩

/-- Paper label: `cor:fiber-gauge-volume-doubling-v2-lowerbound`. -/
theorem paper_fiber_gauge_volume_doubling_v2_lowerbound (m : ℕ) :
    (Finset.univ : Finset (Omega.X m)).sum
        (fun x : Omega.X m => Omega.Folding.basePDigitSum 2 (Omega.X.fiberMultiplicity x)) ≥
      Fintype.card (Omega.X m) := by
  calc
    Fintype.card (Omega.X m) = ∑ x : Omega.X m, 1 := by simp
    _ ≤ ∑ x : Omega.X m, Omega.Folding.basePDigitSum 2 (Omega.X.fiberMultiplicity x) := by
          refine Finset.sum_le_sum ?_
          intro x hx
          exact basePDigitSum_two_one_le (Omega.X.fiberMultiplicity_pos x)

end Omega.Conclusion
