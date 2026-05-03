import Mathlib.Tactic
import Omega.Conclusion.CanonicalSliceExactFixedpointCount
import Omega.Conclusion.CanonicalFixedpointFullshiftConjugacy

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-canonical-fixedpoint-exact-ahlfors-regularity`.
The canonical layer has exactly `(M + 1)^k` cylinders, and the uniform cylinder mass
normalization is exact. -/
theorem paper_conclusion_canonical_fixedpoint_exact_ahlfors_regularity
    (D : CanonicalSliceData) (k : ℕ) :
    Fintype.card (D.fixedPointsAtLayer k) = (D.M + 1) ^ k ∧
      ((D.M + 1 : ℝ) ^ k) * (((D.M + 1 : ℝ)⁻¹) ^ k) = 1 := by
  constructor
  · exact (paper_conclusion_canonical_slice_exact_fixedpoint_count D k).2
  · have hne : (D.M + 1 : ℝ) ≠ 0 := by positivity
    calc
      ((D.M + 1 : ℝ) ^ k) * (((D.M + 1 : ℝ)⁻¹) ^ k)
          = (((D.M + 1 : ℝ) * ((D.M + 1 : ℝ)⁻¹)) ^ k) := by
            rw [mul_pow]
      _ = (1 : ℝ) := by
        rw [mul_inv_cancel₀ hne]
        simp

end Omega.Conclusion
