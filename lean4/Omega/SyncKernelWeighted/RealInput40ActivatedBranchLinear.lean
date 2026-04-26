import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40ActivatedBranchSimplePole

namespace Omega.SyncKernelWeighted

/-- Paper label: `prop:real-input-40-activated-branch-linear`. The activated denominator is
already defined to be the linear factor `u - 1`. -/
theorem paper_real_input_40_activated_branch_linear (u : ℝ) :
    realInput40ActivatedDenominator u = u - 1 := by
  rfl

end Omega.SyncKernelWeighted
