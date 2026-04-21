import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldFiberMultiplicityTraceMoments

open scoped BigOperators

namespace Omega.OperatorAlgebra

noncomputable section

open FoldFiberMultiplicity

/-- The two effective-support readouts for the conditional expectation can be written directly in
terms of the singular-spectrum and multiplicity formulas.
    prop:fold-Em-effective-support-schatten -/
theorem paper_fold_em_effective_support_schatten (D : Omega.OperatorAlgebra.FoldFiberMultiplicity) :
    (((∑ x, (1 / (D.d x : ℝ))) ^ 2) / (∑ x, (1 / (D.d x : ℝ)) ^ 2) =
      ((∑ x, D.singularValue x ^ 2) ^ 2) / (∑ x, D.singularValue x ^ 4)) ∧
      (((∑ x, D.singularValue x) ^ 2) / (∑ x, D.singularValue x ^ 2) =
        ((∑ x, Real.sqrt (1 / (D.d x : ℝ))) ^ 2) / (∑ x, 1 / (D.d x : ℝ))) := by
  have hMoment2 : ∑ x, D.singularValue x ^ 2 = ∑ x, 1 / (D.d x : ℝ) := by
    simpa [FoldFiberMultiplicity.singularNegativeMoment] using
      (paper_fold_fiber_multiplicity_trace_moments D 0 1).2.2
  have hMoment4 : ∑ x, D.singularValue x ^ 4 = ∑ x, (1 / (D.d x : ℝ)) ^ 2 := by
    simpa [FoldFiberMultiplicity.singularNegativeMoment] using
      (paper_fold_fiber_multiplicity_trace_moments D 0 2).2.2
  have hSqrt :
      (∑ x, D.singularValue x) = ∑ x, Real.sqrt (1 / (D.d x : ℝ)) := by
    simp [FoldFiberMultiplicity.singularValue, FoldFiberMultiplicity.diagonalEntry]
  refine ⟨?_, ?_⟩
  · rw [← hMoment2, ← hMoment4]
  · rw [hSqrt, hMoment2]

end

end Omega.OperatorAlgebra
