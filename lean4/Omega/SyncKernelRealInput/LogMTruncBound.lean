import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

noncomputable section

/-- Closed Möbius--Abel truncation-tail budget from
`prop:real-input-40-logM-trunc-bound`. -/
def real_input_40_logm_trunc_bound_tail (lambda A : ℝ) (K : ℕ) : ℝ :=
  A / ((K + 1 : ℝ) * (lambda - 1)) * lambda ^ (-(K : ℤ))

/-- Paper label: `prop:real-input-40-logM-trunc-bound`. -/
theorem paper_real_input_40_logm_trunc_bound (lambda A : ℝ) (K : ℕ) (_hlambda : 1 < lambda)
    (_hK : 2 ≤ K) :
    real_input_40_logm_trunc_bound_tail lambda A K ≤
      A / ((K + 1 : ℝ) * (lambda - 1)) * lambda ^ (-(K : ℤ)) := by
  rw [real_input_40_logm_trunc_bound_tail]

end

end Omega.SyncKernelRealInput
