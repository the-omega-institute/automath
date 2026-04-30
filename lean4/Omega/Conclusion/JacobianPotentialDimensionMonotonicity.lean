import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-jacobian-potential-dimension-monotonicity`.

If the derivative matrix has rank below the source dimension, then its Gram determinant is
singular. -/
theorem paper_conclusion_jacobian_potential_dimension_monotonicity {k l : ℕ}
    (A : Matrix (Fin l) (Fin k) ℝ) (h : A.rank < k) : (A.transpose * A).det = 0 := by
  by_contra hdet
  have hunit_det : IsUnit (A.transpose * A).det := by
    exact isUnit_iff_ne_zero.mpr hdet
  have hunit : IsUnit (A.transpose * A) := by
    exact (Matrix.isUnit_iff_isUnit_det (A.transpose * A)).mpr hunit_det
  have hrank_full : (A.transpose * A).rank = k := by
    simpa using Matrix.rank_of_isUnit (A.transpose * A) hunit
  have hrank_le : (A.transpose * A).rank ≤ A.rank := Matrix.rank_mul_le_right _ _
  omega

end Omega.Conclusion
