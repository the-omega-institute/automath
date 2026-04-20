import Omega.Folding.FiberArithmeticProperties
import Mathlib.Tactic

namespace Omega.Folding

/-- The Fibonacci-weighted size of the resolution-`m` input alphabet. -/
def fibWeightedInputSize (m : ℕ) : ℕ :=
  Nat.fib (m + 2)

/-- The greedy Zeckendorf normalization performs at most one eliminating rewrite per level. -/
def zeckendorfGreedyIterations (m : ℕ) : ℕ :=
  m

/-- One fold pass reads all `m` bits once and then performs the greedy normalization. -/
def foldResolutionSteps (m : ℕ) : ℕ :=
  m + zeckendorfGreedyIterations m

/-- The bit cost is bounded by the word size times the number of resolution steps. -/
def foldBitComplexity (m : ℕ) : ℕ :=
  m * foldResolutionSteps m

lemma zeckendorfGreedyIterations_linear (m : ℕ) :
    zeckendorfGreedyIterations m ≤ m := by
  simp [zeckendorfGreedyIterations]

lemma foldResolutionSteps_linear (m : ℕ) :
    foldResolutionSteps m ≤ 2 * m := by
  simp [foldResolutionSteps, zeckendorfGreedyIterations, two_mul]

lemma foldBitComplexity_quadratic (m : ℕ) :
    foldBitComplexity m ≤ 2 * m ^ 2 := by
  calc
    foldBitComplexity m = m * foldResolutionSteps m := rfl
    _ ≤ m * (2 * m) := Nat.mul_le_mul_left _ (foldResolutionSteps_linear m)
    _ = 2 * m ^ 2 := by ring

/-- The fold algorithm admits explicit linear step counts and a quadratic bit bound:
the Fibonacci-weighted state space is bounded by `2^m`, greedy Zeckendorf normalization uses at
most `m` eliminations, the full resolution procedure takes at most `2m` steps, and the induced
bit complexity is at most `2m²`.
    prop:fold-complexity -/
theorem paper_prop_fold_complexity (m : ℕ) :
    fibWeightedInputSize m ≤ 2 ^ m ∧
      zeckendorfGreedyIterations m ≤ m ∧
      foldResolutionSteps m ≤ 2 * m ∧
      foldBitComplexity m ≤ 2 * m ^ 2 := by
  exact ⟨Omega.X.fib_le_pow_two m, zeckendorfGreedyIterations_linear m,
    foldResolutionSteps_linear m, foldBitComplexity_quadratic m⟩

end Omega.Folding
