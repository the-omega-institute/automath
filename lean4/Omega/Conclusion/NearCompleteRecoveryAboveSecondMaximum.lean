import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic

open Filter

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-near-complete-recovery-above-second-maximum`. -/
theorem paper_conclusion_near_complete_recovery_above_second_maximum
    (Succ defect : ℕ → ℝ) (hSucc : ∀ m, Succ m = 1 - defect m)
    (hDefect : Tendsto defect atTop (nhds 0)) :
    Tendsto Succ atTop (nhds 1) := by
  have hLimit : Tendsto (fun m : ℕ => (1 : ℝ) - defect m) atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub hDefect
  convert hLimit using 1
  · ext m
    exact hSucc m
  · norm_num

end Omega.Conclusion
