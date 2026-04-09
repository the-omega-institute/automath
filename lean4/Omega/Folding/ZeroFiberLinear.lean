import Mathlib.Tactic
import Mathlib.Data.Nat.Fib.Basic

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

end Omega.Folding.ZeroFiberLinear
