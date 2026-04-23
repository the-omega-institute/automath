import Mathlib.Data.Finset.Basic
import Omega.Folding.FiberConvolutionInvertibilityDivisibility

namespace Omega.Folding

/-- Concrete defect statement for the multiplicity convolution invertibility problem: the good
coordinates are exactly the divisor-filtered ones, and their count splits according to whether
`3 ∣ m + 2`. -/
def KilloFoldMultiplicityConvolutionInvertibilityDefect (m : Nat) : Prop :=
  let d := foldFiberCriticalDivisor (m + 2)
  foldFiberGoodCoordinates m = (Finset.Icc 1 m).filter (fun k => d ∣ k + 1) ∧
    if 3 ∣ m + 2 then
      (foldFiberGoodCoordinates m).card = (m + 1) / 6
    else
      (foldFiberGoodCoordinates m).card = (m + 1) / 3

/-- Paper label: `cor:killo-fold-multiplicity-convolution-invertibility-defect`. The Fourier
diagonalization reduces invertibility to the explicit critical divisor, so the good set is read off
from the divisor filter and its size is `(m + 1) / 6` or `(m + 1) / 3` depending on whether
`3 ∣ m + 2`. -/
theorem paper_killo_fold_multiplicity_convolution_invertibility_defect
    (m : Nat) : KilloFoldMultiplicityConvolutionInvertibilityDefect m := by
  dsimp [KilloFoldMultiplicityConvolutionInvertibilityDefect]
  have hSparsity := paper_fold_fiber_invertible_coordinate_sparsity m
  dsimp at hSparsity
  rcases hSparsity with ⟨hGood, hCard⟩
  have hCritical := foldFiberCriticalDivisor_eq (m + 2)
  rw [hCritical] at hCard
  refine ⟨hGood, ?_⟩
  by_cases hThree : 3 ∣ m + 2
  · simpa [hThree] using hCard
  · simpa [hThree] using hCard

end Omega.Folding
