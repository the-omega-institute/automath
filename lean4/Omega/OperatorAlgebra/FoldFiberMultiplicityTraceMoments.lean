import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldConditionalExpectationSingularSpectrum

open scoped BigOperators

namespace Omega.OperatorAlgebra

noncomputable section

namespace FoldFiberMultiplicity

/-- The diagonal multiplicity operator raised to the `t`-th power. -/
def multiplicityDiagonalPow (D : FoldFiberMultiplicity) (t : ℕ) (x : D.X) : ℕ :=
  D.d x ^ t

/-- Finite trace of the `t`-th multiplicity power. -/
def multiplicityTraceMoment (D : FoldFiberMultiplicity) (t : ℕ) : ℕ :=
  ∑ x, D.multiplicityDiagonalPow t x

/-- Schatten-style negative moment computed from the singular values of the conditional
expectation. -/
def singularNegativeMoment (D : FoldFiberMultiplicity) (s : ℕ) : ℝ :=
  ∑ x, D.singularValue x ^ (2 * s)

end FoldFiberMultiplicity

open FoldFiberMultiplicity

/-- For the finite fold-fiber multiplicity package, the diagonal multiplicity operator stays
diagonal after taking powers, its finite trace is the sum of the `q`-th multiplicity moments, and
the `2s`-th singular-value moment is the negative multiplicity moment `∑ d(x)^(-s)`.
    prop:fold-fiber-multiplicity-trace-moments -/
theorem paper_fold_fiber_multiplicity_trace_moments (D : FoldFiberMultiplicity) (q s : ℕ) :
    (∀ x, D.multiplicityDiagonalPow q x = D.d x ^ q) ∧
      D.multiplicityTraceMoment q = ∑ x, D.d x ^ q ∧
      D.singularNegativeMoment s = ∑ x, (1 / (D.d x : ℝ)) ^ s := by
  have hspectrum := paper_prop_fold_conditional_expectation_singular_spectrum D
  have hsq : ∀ x, D.singularValue x ^ 2 = 1 / (D.d x : ℝ) := by
    intro x
    exact (hspectrum.2.2 x).trans (hspectrum.2.1 x)
  refine ⟨?_, rfl, ?_⟩
  · intro x
    rfl
  · unfold FoldFiberMultiplicity.singularNegativeMoment
    refine Finset.sum_congr rfl ?_
    intro x hx
    calc
      D.singularValue x ^ (2 * s) = (D.singularValue x ^ 2) ^ s := by rw [pow_mul]
      _ = (1 / (D.d x : ℝ)) ^ s := by rw [hsq x]

end

end Omega.OperatorAlgebra
