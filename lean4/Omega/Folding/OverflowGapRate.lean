import Mathlib.Tactic
import Omega.Folding.MaxFiberTwoStep

namespace Omega.Folding.OverflowGapRate

open Omega.Folding

/-- Overflow-gap rate identity: `3·A(m) + δ(m) = 2^m` where `δ(m) ∈ {1, 2}`.
    cor:fold-overflow-gap-rate-expectation -/
theorem three_mul_hiddenBitCount_add (m : ℕ) :
    3 * hiddenBitCount m + (if m % 2 = 0 then 1 else 2) = 2 ^ m :=
  paper_hiddenBitCount_closed m

/-- Paper package: overflow gap rate strict bounds.
    cor:fold-overflow-gap-rate-expectation -/
theorem paper_fold_overflow_gap_rate_expectation (m : ℕ) (hm : 2 ≤ m) :
    3 * hiddenBitCount m < 2 ^ m ∧ hiddenBitCount m < 2 ^ m := by
  have h := paper_hiddenBitCount_closed m
  exact ⟨by split_ifs at h <;> omega, hiddenBitCount_lt_pow m hm⟩

end Omega.Folding.OverflowGapRate
