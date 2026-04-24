import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldFiberMultiplicityTraceMoments

open scoped BigOperators

namespace Omega.OperatorAlgebra

noncomputable section

open FoldFiberMultiplicity

lemma singularValue_rpow_eq_multiplicity_rpow (D : FoldFiberMultiplicity) (p : ℝ) (x : D.X) :
    D.singularValue x ^ p = (D.d x : ℝ) ^ (-p / 2) := by
  have hdpos : 0 < (D.d x : ℝ) := by
    exact_mod_cast D.d_pos x
  have hdiag : 0 ≤ 1 / (D.d x : ℝ) := by
    positivity
  calc
    D.singularValue x ^ p = (Real.sqrt (1 / (D.d x : ℝ))) ^ p := by
      simp [FoldFiberMultiplicity.singularValue, FoldFiberMultiplicity.diagonalEntry]
    _ = (1 / (D.d x : ℝ)) ^ ((1 / 2 : ℝ) * p) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hdiag (1 / 2 : ℝ) p]
    _ = (1 / (D.d x : ℝ)) ^ (p / 2) := by
      congr 1
      ring
    _ = ((D.d x : ℝ) ^ (p / 2))⁻¹ := by
      rw [one_div, Real.inv_rpow (le_of_lt hdpos)]
    _ = (D.d x : ℝ) ^ (-(p / 2)) := by
      rw [← Real.rpow_neg (le_of_lt hdpos)]
    _ = (D.d x : ℝ) ^ (-p / 2) := by
      congr 1
      ring

/-- The Schatten `p`-moment of the finite fold conditional expectation equals the corresponding
negative multiplicity moment.
    cor:fold-conditional-expectation-schatten -/
theorem paper_fold_conditional_expectation_schatten (D : FoldFiberMultiplicity) (p : ℝ) :
    (∑ x, D.singularValue x ^ p) = ∑ x, (D.d x : ℝ) ^ (-p / 2) := by
  refine Finset.sum_congr rfl ?_
  intro x hx
  exact singularValue_rpow_eq_multiplicity_rpow D p x

end

end Omega.OperatorAlgebra
