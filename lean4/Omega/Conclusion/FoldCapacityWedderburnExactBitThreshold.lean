import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
import Omega.Conclusion.CausalDepthBranchBudgetOrthogonality

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-fold-capacity-wedderburn-exact-bit-threshold`.
The dyadic exact-inversion threshold is the binary ceiling `⌈log₂ d_max⌉`, expressed here via the
equivalent inequality `d_max ≤ 2^B`. -/
theorem paper_conclusion_fold_capacity_wedderburn_exact_bit_threshold
    (dmax B : Nat) (hdmax : 0 < dmax) :
    dmax <= 2 ^ B ↔ Nat.ceil (Real.log (dmax : Real) / Real.log 2) <= B := by
  let _ := hdmax
  have hceil : Nat.ceil (Real.logb 2 (dmax : Real)) = Nat.clog 2 dmax := by
    simpa using (Real.natCeil_logb_natCast 2 dmax)
  simpa [Real.log_div_log, hceil, FiberDistinguishableWithBudget, fiberBranchBudget] using
    (fiberBranchBudget_iff_distinguishable dmax B)

/-- Window-`6` specialization of the exact-bit threshold: the audited maximal fiber size `4`
requires exactly `2` auxiliary bits. -/
theorem conclusion_fold_capacity_wedderburn_exact_bit_threshold_window6 :
    Nat.ceil (Real.log ((4 : Nat) : Real) / Real.log 2) = 2 := by
  have hceil : Nat.ceil (Real.logb 2 ((4 : Nat) : Real)) = Nat.clog 2 4 := by
    simpa using (Real.natCeil_logb_natCast 2 4)
  rw [Real.log_div_log, hceil]
  norm_num

end Omega.Conclusion
