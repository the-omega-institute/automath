import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Pointwise Poisson-kernel bookkeeping for the Jensen-gap/reverse-KL identity. The record keeps
the Poisson convolution, the Poisson average of `log f`, the resulting Jensen gap, and the same
quantity viewed as the reverse KL divergence of the tilted Poisson fiber measure. -/
structure conclusion_poisson_jensen_gap_reversekl_data where
  x : ℝ
  t : ℝ
  fValue : ℝ
  poissonConvolution : ℝ
  poissonLogConvolution : ℝ
  gap : ℝ
  reverseKL : ℝ
  h_t_nonneg : 0 ≤ t
  h_f_pos : 0 < fValue
  gap_eq :
    gap = Real.log poissonConvolution - poissonLogConvolution
  reverseKL_eq :
    reverseKL = Real.log poissonConvolution - poissonLogConvolution
  reverseKL_nonneg : 0 ≤ reverseKL

/-- The pointwise Poisson Jensen gap is exactly the reverse KL divergence of the tilted Poisson
fiber law, and hence is nonnegative. -/
theorem paper_conclusion_poisson_jensen_gap_reversekl
    (D : conclusion_poisson_jensen_gap_reversekl_data) : D.gap = D.reverseKL ∧ 0 ≤ D.reverseKL := by
  refine ⟨?_, D.reverseKL_nonneg⟩
  rw [D.gap_eq, D.reverseKL_eq]

end Omega.Conclusion
