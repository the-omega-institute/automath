import Mathlib.Tactic
import Omega.Conclusion.HydrogenicClassfunctionAverageResidualLogarithm
import Omega.Conclusion.HydrogenicPhaseblindAverageResidualBits

namespace Omega.Conclusion

noncomputable section

def conclusion_hydrogenic_worst_average_budget_gap_classFunctionGap (n : ℕ) : ℝ :=
  conclusion_hydrogenic_classfunction_average_residual_logarithm_entropy n -
    (conclusion_hydrogenic_phaseblind_average_residual_bits_average n : ℝ)

def conclusion_hydrogenic_worst_average_budget_gap_statement (n : ℕ) : Prop :=
  conclusion_hydrogenic_phaseblind_average_residual_bits_statement n ∧
    conclusion_hydrogenic_classfunction_average_residual_logarithm_statement n ∧
    conclusion_hydrogenic_phaseblind_average_residual_bits_average n = 2 - 1 / (n : ℚ) ∧
    conclusion_hydrogenic_worst_average_budget_gap_classFunctionGap n =
      conclusion_hydrogenic_classfunction_average_residual_logarithm_entropy n -
        (2 - 1 / (n : ℚ) : ℚ) ∧
    conclusion_hydrogenic_classfunction_average_residual_logarithm_entropy n =
      Real.log (n : ℝ) / Real.log 2 +
        conclusion_hydrogenic_classfunction_average_residual_logarithm_midpointRemainder n

/-- Paper label: `prop:conclusion-hydrogenic-worst-average-budget-gap`. -/
theorem paper_conclusion_hydrogenic_worst_average_budget_gap (n : ℕ) (hn : 0 < n) :
    conclusion_hydrogenic_worst_average_budget_gap_statement n := by
  have hphase := paper_conclusion_hydrogenic_phaseblind_average_residual_bits n hn
  have hclass := paper_conclusion_hydrogenic_classfunction_average_residual_logarithm n hn
  refine ⟨hphase, hclass, hphase.2.2.2.2, ?_, hclass.2.2.1⟩
  unfold conclusion_hydrogenic_worst_average_budget_gap_classFunctionGap
  rw [hphase.2.2.2.2]

end

end Omega.Conclusion
