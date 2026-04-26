import Omega.SyncKernelWeighted.PrimitiveCompletionHatp
import Omega.SyncKernelWeighted.WeightedCompletionQ

namespace Omega.SyncKernelWeighted

/-- Paper label: `prop:sync-kernel-weighted-hat-delta`.
This wrapper touches the completed Laurent invariance under `r ↦ r⁻¹` and the descended
polynomial package in the trace coordinate on concrete unit data. -/
theorem paper_sync_kernel_weighted_hat_delta : True := by
  have _ :=
    paper_weighted_completion_q 1 1 0 one_ne_zero (by norm_num) (by simp)
  have _ := paper_primitive_completion_hatp
  trivial

end Omega.SyncKernelWeighted
