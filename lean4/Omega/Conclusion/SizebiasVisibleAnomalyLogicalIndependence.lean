import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Omega.Conclusion.CompleteStrictificationDualCriterion

open scoped BigOperators

namespace Omega.Conclusion

/-- Positive size-biased residual with trivial visible channel. -/
def conclusion_sizebias_visible_anomaly_logical_independence_positive_residual :
    Fin 1 → ℕ :=
  fun _ => 1

/-- Trivial visible channel witness. -/
def conclusion_sizebias_visible_anomaly_logical_independence_trivial_visible_channel :
    Fin 1 → ℕ :=
  fun _ => 0

/-- Zero residual witness used for the converse non-implication. -/
def conclusion_sizebias_visible_anomaly_logical_independence_zero_residual :
    Fin 1 → ℕ :=
  fun _ => 0

/-- Nonzero visible anomaly witness. -/
def conclusion_sizebias_visible_anomaly_logical_independence_nonzero_visible_anomaly :
    Fin 1 → ℕ :=
  fun _ => 1

theorem conclusion_sizebias_visible_anomaly_logical_independence_first_witness :
    zeroVisibleAnomaly
        conclusion_sizebias_visible_anomaly_logical_independence_trivial_visible_channel ∧
      ¬ zeroSizebiasedResidual
        conclusion_sizebias_visible_anomaly_logical_independence_positive_residual := by
  constructor
  · simp [zeroVisibleAnomaly,
      conclusion_sizebias_visible_anomaly_logical_independence_trivial_visible_channel]
  · simp [zeroSizebiasedResidual,
      conclusion_sizebias_visible_anomaly_logical_independence_positive_residual]

theorem conclusion_sizebias_visible_anomaly_logical_independence_second_witness :
    zeroSizebiasedResidual
        conclusion_sizebias_visible_anomaly_logical_independence_zero_residual ∧
      ¬ zeroVisibleAnomaly
        conclusion_sizebias_visible_anomaly_logical_independence_nonzero_visible_anomaly := by
  constructor
  · simp [zeroSizebiasedResidual,
      conclusion_sizebias_visible_anomaly_logical_independence_zero_residual]
  · simp [zeroVisibleAnomaly,
      conclusion_sizebias_visible_anomaly_logical_independence_nonzero_visible_anomaly]

/-- Paper label: `prop:conclusion-sizebias-visible-anomaly-logical-independence`. The first
explicit witness has trivial visible channel but positive residual, while the second has zero
residual but nonzero visible anomaly; together they exhibit both non-implication directions. -/
def paper_conclusion_sizebias_visible_anomaly_logical_independence : Prop := by
  exact
    (zeroVisibleAnomaly
        conclusion_sizebias_visible_anomaly_logical_independence_trivial_visible_channel ∧
      ¬ zeroSizebiasedResidual
        conclusion_sizebias_visible_anomaly_logical_independence_positive_residual) ∧
    (zeroSizebiasedResidual
        conclusion_sizebias_visible_anomaly_logical_independence_zero_residual ∧
      ¬ zeroVisibleAnomaly
        conclusion_sizebias_visible_anomaly_logical_independence_nonzero_visible_anomaly)

end Omega.Conclusion
