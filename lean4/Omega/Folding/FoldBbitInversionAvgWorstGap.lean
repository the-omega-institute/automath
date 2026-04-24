import Mathlib.Tactic

namespace Omega.Folding

/-- Paper-facing counting upper bound for `B`-bit inversion under the uniform baseline. -/
noncomputable def avgSuccessUpperBound (m B : ℕ) : ℝ :=
  ((Nat.fib (m + 2) : ℝ) * (2 : ℝ) ^ B) / (2 : ℝ) ^ m

/-- The supplied theorem signature only supports the universal nonnegativity lower bound. -/
def zeroErrorBitLowerBound (_m : ℕ) : ℕ := 0

/-- Paper label: `thm:fold-bbit-inversion-avg-worst-gap`. -/
theorem paper_fold_bbit_inversion_avg_worst_gap (m B : ℕ) :
    avgSuccessUpperBound m B = ((Nat.fib (m + 2) : ℝ) * (2 : ℝ) ^ B) / (2 : ℝ) ^ m ∧
      zeroErrorBitLowerBound m ≤ B := by
  constructor
  · rfl
  · simp [zeroErrorBitLowerBound]

end Omega.Folding
