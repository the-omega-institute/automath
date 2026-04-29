import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Conclusion.HydrogenicClassfunctionAverageResidualLogarithm
import Omega.Conclusion.HydrogenicPhaseblindAverageResidualBits

namespace Omega.Conclusion

noncomputable section

/-- The extra residual budget paid by the class-function projection over the phase-blind one. -/
def conclusion_hydrogenic_divergent_hidden_cost_from_nonabelian_blocks_hiddenCost
    (n : ℕ) : ℝ :=
  conclusion_hydrogenic_classfunction_average_residual_logarithm_entropy n -
    (conclusion_hydrogenic_phaseblind_average_residual_bits_average n : ℝ)

/-- The finite algebraic remainder after subtracting the phase-blind residual formula from the
class-function logarithmic residual package. -/
def conclusion_hydrogenic_divergent_hidden_cost_from_nonabelian_blocks_remainder
    (n : ℕ) : ℝ :=
  conclusion_hydrogenic_classfunction_average_residual_logarithm_midpointRemainder n -
    (2 - 1 / (n : ℝ))

/-- Concrete statement for the divergent hidden cost: the class-function residual equals the
phase-blind residual plus a leading `log₂ n` term and the finite midpoint remainder. -/
def conclusion_hydrogenic_divergent_hidden_cost_from_nonabelian_blocks_statement
    (n : ℕ) : Prop :=
  conclusion_hydrogenic_divergent_hidden_cost_from_nonabelian_blocks_hiddenCost n =
    Real.log (n : ℝ) / Real.log 2 +
      conclusion_hydrogenic_divergent_hidden_cost_from_nonabelian_blocks_remainder n

/-- Paper label:
`cor:conclusion-hydrogenic-divergent-hidden-cost-from-nonabelian-blocks`. -/
theorem paper_conclusion_hydrogenic_divergent_hidden_cost_from_nonabelian_blocks
    (n : ℕ) (hn : 0 < n) :
    conclusion_hydrogenic_divergent_hidden_cost_from_nonabelian_blocks_statement n := by
  have hclass :=
    paper_conclusion_hydrogenic_classfunction_average_residual_logarithm n hn
  have hphase := paper_conclusion_hydrogenic_phaseblind_average_residual_bits n hn
  have hphaseReal :
      (conclusion_hydrogenic_phaseblind_average_residual_bits_average n : ℝ) =
        2 - 1 / (n : ℝ) := by
    norm_num [hphase.2.2.2.2]
  unfold conclusion_hydrogenic_divergent_hidden_cost_from_nonabelian_blocks_statement
  unfold conclusion_hydrogenic_divergent_hidden_cost_from_nonabelian_blocks_hiddenCost
  unfold conclusion_hydrogenic_divergent_hidden_cost_from_nonabelian_blocks_remainder
  rw [hclass.2.2.1, hphaseReal]
  ring

end

end Omega.Conclusion
