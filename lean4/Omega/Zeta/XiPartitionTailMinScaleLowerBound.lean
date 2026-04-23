import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Omega.Zeta

/-- Concrete data for the logarithmic observation-scale lower bound extracted from an exponential
tail-separation estimate. -/
structure xi_partition_tail_min_scale_lower_bound_data where
  deltaMin : ℝ
  epsilon : ℝ
  maxScale : ℝ
  hdelta : 0 < deltaMin
  heps0 : 0 < epsilon
  heps1 : epsilon < 1
  htail : Real.exp (-maxScale * deltaMin) ≤ epsilon

/-- The observation horizon must dominate the logarithmic separation scale. -/
def xi_partition_tail_min_scale_lower_bound_statement
    (h : xi_partition_tail_min_scale_lower_bound_data) : Prop :=
  Real.log (1 / h.epsilon) / h.deltaMin ≤ h.maxScale

/-- Paper label: `cor:xi-partition-tail-min-scale-lower-bound`. -/
theorem paper_xi_partition_tail_min_scale_lower_bound
    (h : xi_partition_tail_min_scale_lower_bound_data) :
    xi_partition_tail_min_scale_lower_bound_statement h := by
  unfold xi_partition_tail_min_scale_lower_bound_statement
  have hlog : -h.maxScale * h.deltaMin ≤ Real.log h.epsilon := by
    exact (Real.le_log_iff_exp_le h.heps0).2 h.htail
  have hbound : Real.log (1 / h.epsilon) ≤ h.maxScale * h.deltaMin := by
    calc
      Real.log (1 / h.epsilon) = -Real.log h.epsilon := by rw [one_div, Real.log_inv]
      _ ≤ -(-h.maxScale * h.deltaMin) := neg_le_neg hlog
      _ = h.maxScale * h.deltaMin := by simp
  apply (div_le_iff₀ h.hdelta).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hbound

end Omega.Zeta
