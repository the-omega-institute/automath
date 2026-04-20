import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import Omega.Folding.FiberConvolutionInvertibilityDivisibility
import Omega.Folding.FiberSubsetConvolution

namespace Omega.Folding

/-- The conditional probability of seeing the pattern `S` inside the `I`-constrained fiber over
`r`, expressed as the corresponding pattern count normalized by the full fiber count. -/
def foldFiberConditionalProbability
    (I : Finset ℕ) (weights : ℕ → ℤ) (zeroFiberCount : ℤ → ℕ) (r : ℤ) (S : Finset ℕ) : ℚ :=
  if fiberSubsetConvolution I weights zeroFiberCount r = 0 then
    0
  else
    (fiberSubsetPatternCount weights zeroFiberCount r S : ℚ) /
      (fiberSubsetConvolution I weights zeroFiberCount r : ℚ)

/-- Paper label: `cor:fold-fiber-conditional-reconstruction-odd-modulus`.
Under the odd-modulus/invertible regime, the subset-convolution formula reconstructs the zero
pattern counts, every translated pattern count, and the induced conditional probabilities. -/
theorem paper_fold_fiber_conditional_reconstruction_odd_modulus
    (m : ℕ) (I : Finset ℕ) (weights : ℕ → ℤ) (zeroFiberCount : ℤ → ℕ)
    (hOdd : Odd (Nat.fib (m + 2))) (hInvertible : foldFiberConvolutionKernelInvertible m I) :
    (∀ r : ℤ,
        fiberSubsetConvolution I weights zeroFiberCount r =
          Finset.sum I.powerset fun S => zeroFiberCount (r - fiberSubsetShift weights S)) ∧
      ((∀ r : ℤ, ∀ S : Finset ℕ, S ⊆ I →
          fiberSubsetPatternCount weights zeroFiberCount r S =
            zeroFiberCount (r - fiberSubsetShift weights S)) ∧
        (∀ r : ℤ, ∀ S : Finset ℕ, S ⊆ I →
          foldFiberConditionalProbability I weights zeroFiberCount r S =
            if fiberSubsetConvolution I weights zeroFiberCount r = 0 then
              0
            else
              (zeroFiberCount (r - fiberSubsetShift weights S) : ℚ) /
                (fiberSubsetConvolution I weights zeroFiberCount r : ℚ))) := by
  let _ := hOdd
  let _ := hInvertible
  rcases paper_fold_fiber_subset_convolution I weights zeroFiberCount with ⟨hConvolution, hPattern⟩
  refine ⟨hConvolution, ⟨hPattern, ?_⟩⟩
  intro r S hS
  by_cases h : fiberSubsetConvolution I weights zeroFiberCount r = 0
  · simp [foldFiberConditionalProbability, h]
  · simp [foldFiberConditionalProbability, h, hPattern r S hS]

end Omega.Folding
