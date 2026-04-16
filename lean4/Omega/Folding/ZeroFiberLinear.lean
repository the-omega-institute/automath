import Mathlib.Tactic
import Mathlib.Data.Nat.Fib.Basic
import Omega.Folding.FiberWeightCount

namespace Omega.Folding.ZeroFiberLinear

/-- Weight sum count at level `m`: number of Boolean strings of length `m`
    with Zeckendorf-weight sum equal to `fib (m+2)`.
    prop:fold-zero-fiber-linear -/
def weightSumAtMm (m : Nat) : Nat :=
  ((Finset.univ : Finset (Fin m → Bool)).filter
    (fun ω => (Finset.univ : Finset (Fin m)).sum
      (fun k => if ω k then Nat.fib (k.val + 2) else 0) = Nat.fib (m + 2))).card

/-- Concrete m=2 case: `weightSumAtMm 2 = 1`.
    prop:fold-zero-fiber-linear -/
theorem weightSumAtMm_two : weightSumAtMm 2 = 1 := by
  decide

/-- Concrete m=3 case: `weightSumAtMm 3 = 1`.
    prop:fold-zero-fiber-linear -/
theorem weightSumAtMm_three : weightSumAtMm 3 = 1 := by
  decide

/-- Concrete m=4 case: `weightSumAtMm 4 = 2`.
    prop:fold-zero-fiber-linear -/
theorem weightSumAtMm_four : weightSumAtMm 4 = 2 := by
  decide

/-- Concrete m=5 case: `weightSumAtMm 5 = 2`.
    prop:fold-zero-fiber-linear -/
theorem weightSumAtMm_five : weightSumAtMm 5 = 2 := by
  decide

/-- Closed form verified at `m = 2, 3, 4, 5`: `weightSumAtMm m = m / 2`.
    prop:fold-zero-fiber-linear -/
theorem weightSumAtMm_eq_div_two_small :
    weightSumAtMm 2 = 2 / 2 ∧
    weightSumAtMm 3 = 3 / 2 ∧
    weightSumAtMm 4 = 4 / 2 ∧
    weightSumAtMm 5 = 5 / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [weightSumAtMm_two]
  · rw [weightSumAtMm_three]
  · rw [weightSumAtMm_four]
  · rw [weightSumAtMm_five]

/-- Paper package (concrete small-m verification): zero-fiber linearity
    `1 + ⌊m/2⌋` verified for `m = 2, 3, 4, 5`.
    prop:fold-zero-fiber-linear -/
theorem paper_fold_zero_fiber_linear_small :
    (1 + weightSumAtMm 2 = 1 + 2 / 2) ∧
    (1 + weightSumAtMm 3 = 1 + 3 / 2) ∧
    (1 + weightSumAtMm 4 = 1 + 4 / 2) ∧
    (1 + weightSumAtMm 5 = 1 + 5 / 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals (simp [weightSumAtMm_two, weightSumAtMm_three,
                   weightSumAtMm_four, weightSumAtMm_five])

/-- Concrete m=6 case: `weightSumAtMm 6 = 3`.
    prop:fold-zero-fiber-linear -/
theorem weightSumAtMm_six : weightSumAtMm 6 = 3 := by native_decide

/-- Concrete m=7 case: `weightSumAtMm 7 = 3`.
    prop:fold-zero-fiber-linear -/
theorem weightSumAtMm_seven : weightSumAtMm 7 = 3 := by native_decide

/-- Concrete m=8 case: `weightSumAtMm 8 = 4`.
    prop:fold-zero-fiber-linear -/
theorem weightSumAtMm_eight : weightSumAtMm 8 = 4 := by native_decide

/-- Step recurrence: weightSumAtMm(m+2) = weightSumAtMm(m) + 1 for m = 2..6.
    prop:fold-zero-fiber-linear -/
theorem weightSumAtMm_step_recurrence :
    weightSumAtMm 4 = weightSumAtMm 2 + 1 ∧
    weightSumAtMm 5 = weightSumAtMm 3 + 1 ∧
    weightSumAtMm 6 = weightSumAtMm 4 + 1 ∧
    weightSumAtMm 7 = weightSumAtMm 5 + 1 ∧
    weightSumAtMm 8 = weightSumAtMm 6 + 1 := by
  rw [weightSumAtMm_two, weightSumAtMm_three, weightSumAtMm_four,
      weightSumAtMm_five, weightSumAtMm_six, weightSumAtMm_seven,
      weightSumAtMm_eight]; decide

/-- Closed form at m = 6, 7, 8: weightSumAtMm m = m / 2.
    prop:fold-zero-fiber-linear -/
theorem weightSumAtMm_eq_div_two_extended :
    weightSumAtMm 6 = 6 / 2 ∧
    weightSumAtMm 7 = 7 / 2 ∧
    weightSumAtMm 8 = 8 / 2 := by
  rw [weightSumAtMm_six, weightSumAtMm_seven, weightSumAtMm_eight]; decide

/-- Paper package: zero-fiber linearity extended seeds m = 2..8.
    prop:fold-zero-fiber-linear -/
theorem paper_fold_zero_fiber_linear_extended :
    weightSumAtMm 2 = 1 ∧ weightSumAtMm 3 = 1 ∧
    weightSumAtMm 4 = 2 ∧ weightSumAtMm 5 = 2 ∧
    weightSumAtMm 6 = 3 ∧ weightSumAtMm 7 = 3 ∧
    weightSumAtMm 8 = 4 ∧
    (weightSumAtMm 4 = weightSumAtMm 2 + 1 ∧
     weightSumAtMm 6 = weightSumAtMm 4 + 1 ∧
     weightSumAtMm 8 = weightSumAtMm 6 + 1) :=
  ⟨weightSumAtMm_two, weightSumAtMm_three,
   weightSumAtMm_four, weightSumAtMm_five,
   weightSumAtMm_six, weightSumAtMm_seven,
   weightSumAtMm_eight,
   weightSumAtMm_step_recurrence.1,
   weightSumAtMm_step_recurrence.2.2.1,
   weightSumAtMm_step_recurrence.2.2.2.2⟩

/-- `weightSumAtMm` is exactly the exact-weight count at the Fibonacci threshold. -/
theorem weightSumAtMm_eq_exactWeightCount (m : Nat) :
    weightSumAtMm m = Omega.exactWeightCount m (Nat.fib (m + 2)) := by
  unfold weightSumAtMm Omega.exactWeightCount
  congr 1
  ext w
  simp [Omega.weight_eq_fib_ite_sum]

/-- Paper package: the zero fiber has size `1 + ⌊m / 2⌋` for all `m ≥ 2`.
    prop:fold-zero-fiber-linear -/
theorem paper_fold_zero_fiber_linear (m : Nat) (hm : 2 ≤ m) :
    1 + Omega.Folding.ZeroFiberLinear.weightSumAtMm m = 1 + m / 2 := by
  have hm' : 2 ≤ m := hm
  rw [weightSumAtMm_eq_exactWeightCount, Omega.exactWeightCount_fib_closed]

end Omega.Folding.ZeroFiberLinear
