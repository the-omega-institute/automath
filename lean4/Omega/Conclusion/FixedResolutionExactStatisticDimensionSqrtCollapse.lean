import Mathlib.Tactic
import Omega.Folding.MaxFiberHigh

namespace Omega.Conclusion

/-- Concrete fixed-resolution statistic data: `multiplicityCount` is the number `s_m` of distinct
positive fiber multiplicities, and `maxMultiplicity` is the maximum fiber multiplicity `D_m`. -/
structure conclusion_fixedresolution_exact_statistic_dimension_squareroot_collapse_data where
  multiplicityCount : ℕ
  maxMultiplicity : ℕ
  multiplicityCount_le_max : multiplicityCount ≤ maxMultiplicity

/-- The exact nontrivial statistic dimension `2 s_m - 2`. -/
def conclusion_fixedresolution_exact_statistic_dimension_squareroot_collapse_exactDimension
    (D : conclusion_fixedresolution_exact_statistic_dimension_squareroot_collapse_data) : ℕ :=
  2 * D.multiplicityCount - 2

/-- The finite-core inequality, together with the existing even and odd Fibonacci closed forms for
the fold max-fiber multiplicity in the verified finite range. -/
def conclusion_fixedresolution_exact_statistic_dimension_squareroot_collapse_statement
    (D : conclusion_fixedresolution_exact_statistic_dimension_squareroot_collapse_data) : Prop :=
  conclusion_fixedresolution_exact_statistic_dimension_squareroot_collapse_exactDimension D ≤
      2 * D.maxMultiplicity - 2 ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ 5 →
      Omega.X.maxFiberMultiplicity (2 * k) = Nat.fib (k + 2)) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ 4 →
      Omega.X.maxFiberMultiplicity (2 * k + 1) = 2 * Nat.fib (k + 1))

/-- Paper label: `cor:conclusion-fixedresolution-exact-statistic-dimension-squareroot-collapse`. -/
theorem paper_conclusion_fixedresolution_exact_statistic_dimension_squareroot_collapse
    (D : conclusion_fixedresolution_exact_statistic_dimension_squareroot_collapse_data) :
    conclusion_fixedresolution_exact_statistic_dimension_squareroot_collapse_statement D := by
  refine ⟨?_, ?_, ?_⟩
  · unfold conclusion_fixedresolution_exact_statistic_dimension_squareroot_collapse_exactDimension
    exact Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 D.multiplicityCount_le_max) 2
  · intro k hk hk'
    exact Omega.X.maxFiberMultiplicity_even_ext k hk hk'
  · intro k hk hk'
    exact Omega.X.maxFiberMultiplicity_odd_ext k hk hk'

end Omega.Conclusion
