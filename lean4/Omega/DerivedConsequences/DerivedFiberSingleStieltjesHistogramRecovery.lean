import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldConditionalExpectationSpectrumHistogram
import Omega.OperatorAlgebra.FoldFiberMultiplicityTraceMoments

namespace Omega.DerivedConsequences

open Omega.OperatorAlgebra
open Omega.OperatorAlgebra.FoldFiberMultiplicity

/-- Paper label: `thm:derived-fiber-single-stieltjes-histogram-recovery`.
For the canonical finite fold model with multiplicity degrees `1, ..., m`, the first Stieltjes
sum is exactly the first singular negative moment, inverse squares of singular values recover the
degrees, and the existing logarithmic triangularity package recovers the histogram uniquely. -/
theorem paper_derived_fiber_single_stieltjes_histogram_recovery {m : ℕ}
    (N : FoldOrbitHistogram m) :
    let D := foldConditionalExpectationSpectrumModel m
    D.singularNegativeMoment 1 = ∑ x : Fin m, 1 / (foldOrbitDegree x : ℝ) ∧
      (∀ x : Fin m, ((D.singularValue x) ^ 2)⁻¹ = foldOrbitDegree x) ∧
      FoldOrbitFactorizationFormula N ∧
      FoldOrbitTriangularRecursion N ∧
      FoldOrbitHistogramUnique N := by
  dsimp
  let D := foldConditionalExpectationSpectrumModel m
  have hMoment := paper_fold_fiber_multiplicity_trace_moments D 0 1
  have hHistogram := paper_fold_conditional_expectation_spectrum_histogram N
  refine ⟨?_, hHistogram.1, hHistogram.2.1, hHistogram.2.2.1, hHistogram.2.2.2⟩
  simpa [D, pow_one] using hMoment.2.2

end Omega.DerivedConsequences
