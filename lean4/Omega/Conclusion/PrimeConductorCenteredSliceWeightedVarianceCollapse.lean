import Mathlib

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label:
`cor:conclusion-prime-conductor-centered-slice-weighted-variance-collapse`. -/
theorem paper_conclusion_prime_conductor_centered_slice_weighted_variance_collapse
    {ι : Type*} [Fintype ι] (W V : ι → ℝ) (C wStar : ℝ)
    (hw : ∀ r, wStar ≤ W r) (hwpos : 0 < wStar)
    (hweighted : (∑ r, W r * V r ^ 2) ≤ C) :
    (∑ r, V r ^ 2) ≤ C / wStar := by
  classical
  have hterm : (∑ r, wStar * V r ^ 2) ≤ ∑ r, W r * V r ^ 2 := by
    exact Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_right (hw r) (sq_nonneg (V r))
  have hscaled : wStar * (∑ r, V r ^ 2) ≤ C := by
    have hterm' : wStar * (∑ r, V r ^ 2) ≤ ∑ r, W r * V r ^ 2 := by
      simpa [Finset.mul_sum] using hterm
    exact hterm'.trans hweighted
  rw [le_div_iff₀ hwpos]
  simpa [mul_comm] using hscaled

end Omega.Conclusion
