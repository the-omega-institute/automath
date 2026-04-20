import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Omega.Zeta.DerivedLeyangBranchsetAdjacencySpectrumHeatTrace

namespace Omega.Conclusion

/-- Specializing the Lee--Yang branchset heat-trace identity at `-t` gives the partition function,
and setting `t = 0` recovers the exact state count `5 * 4^n`.
    thm:conclusion-leyang-five-hypercube-partition-splitting -/
theorem paper_conclusion_leyang_five_hypercube_partition_splitting (n : Nat) (t : Real) :
    Omega.Zeta.leyangBranchsetHeatTrace n (-t) = 5 * (2 * Real.cosh t) ^ (2 * n) ∧
      Omega.Zeta.leyangBranchsetHeatTrace n 0 = 5 * 4 ^ n := by
  refine ⟨?_, ?_⟩
  · simpa [Real.cosh_neg] using Omega.Zeta.leyang_heat_trace_closed_form n (-t)
  · have hzero := Omega.Zeta.leyang_heat_trace_closed_form n 0
    calc
      Omega.Zeta.leyangBranchsetHeatTrace n 0 = 5 * (2 ^ 2) ^ n := by
        simpa [pow_mul] using hzero
      _ = 5 * 4 ^ n := by norm_num

end Omega.Conclusion
