import Mathlib
import Omega.Conclusion.RamanujanCollapse
import Omega.Kronecker.W1FibonacciLimits
import Omega.Kronecker.W1RightShiftedMinimizer

namespace Omega.Conclusion

/-- The golden transport/star package records the good-side star budget at `q = 2`, the explicit
right-shifted transport branching ratio, the even/odd Fibonacci transport constants, and the
positivity of the logarithmic overhead constant. -/
def conclusion_golden_transport_star_log_overhead_spec : Prop :=
  Omega.Kronecker.kroneckerGoodSideStarDiscrepancy 2 = (1 : ℚ) / 2 ∧
    Omega.Kronecker.kroneckerRightShiftedBranchingRatio 2 = (3 : ℚ) / 4 ∧
    ((Omega.Kronecker.kroneckerGoodSideStarDiscrepancy 2 : ℚ) <
      Omega.Kronecker.kroneckerRightShiftedBranchingRatio 2) ∧
    Omega.Kronecker.goldenEvenScaledLimitConstant = (1 / 2 : ℝ) + 1 / (2 * Real.sqrt 5) ∧
    Omega.Kronecker.goldenOddScaledLimitConstant =
      (1 / 2 : ℝ) - 1 / (2 * Real.sqrt 5) + 1 / 15 ∧
    Real.log (2 / Real.sqrt Real.goldenRatio) / Real.log Real.goldenRatio =
      Real.log 2 / Real.log Real.goldenRatio - 1 / 2 ∧
    0 < Real.log (2 / Real.sqrt Real.goldenRatio) / Real.log Real.goldenRatio

theorem paper_conclusion_golden_transport_star_log_overhead :
    conclusion_golden_transport_star_log_overhead_spec := by
  rcases Omega.Kronecker.paper_xi_kronecker_star_discrepancy_w1_branching 2 (by norm_num) with
    ⟨_, _, _, hstar, hratio⟩
  rcases Omega.Kronecker.paper_kronecker_w1_fibonacci_limits with ⟨heven, hodd⟩
  have hratio_gt_one : 1 < Real.log 2 / Real.log Real.goldenRatio := by
    have hphi_pos : 0 < Real.goldenRatio := Real.goldenRatio_pos
    have hlogphi_pos : 0 < Real.log Real.goldenRatio := Real.log_pos Real.one_lt_goldenRatio
    have hlogphi_lt : Real.log Real.goldenRatio < Real.log 2 := by
      exact Real.log_lt_log hphi_pos Real.goldenRatio_lt_two
    refine (lt_div_iff₀ hlogphi_pos).2 ?_
    simpa using hlogphi_lt
  have hratio' : Omega.Kronecker.kroneckerRightShiftedBranchingRatio 2 = (3 : ℚ) / 4 := by
    calc
      Omega.Kronecker.kroneckerRightShiftedBranchingRatio 2 = (9 : ℚ) / 12 := by
        simpa using hratio
      _ = (3 : ℚ) / 4 := by norm_num
  refine ⟨by simpa using hstar, hratio', ?_, heven, hodd,
    paper_ramanujan_half_dimension_collapse, ?_⟩
  · rw [hstar, hratio]
    norm_num
  · rw [paper_ramanujan_half_dimension_collapse]
    linarith

end Omega.Conclusion
