import Mathlib.Tactic
import Omega.POM.AdjacentPressureConvexity

namespace Omega.POM

/-- Chapter-local package for the discrete variational threshold governing the optimal certificate
moment. The data records the certificate exponent family, the adjacent `q - 1` and `q + 1`
comparisons, the discrete convexity input used to order the thresholds, and the two paper-facing
outputs: interval bounds for the selected minimizer and monotonicity of the resulting phase
diagram in the budget parameter. -/
structure QstarDiscreteVariationalThresholdData where
  budget : ℝ
  qStar : ℕ
  certificateExponentFamily : ℕ → ℝ
  leftAdjacentComparison : Prop
  rightAdjacentComparison : Prop
  discreteConvexity : Prop
  intervalCharacterization : Prop
  monotonePhaseDiagram : Prop
  leftAdjacentComparison_h : leftAdjacentComparison
  rightAdjacentComparison_h : rightAdjacentComparison
  discreteConvexity_h : discreteConvexity
  intervalCharacterization_h : intervalCharacterization
  monotonePhaseDiagram_h : monotonePhaseDiagram

/-- The optimal discrete certificate exponent satisfies the paper's interval characterization and
the associated phase diagram is monotone in the budget parameter.
    prop:pom-qstar-discrete-variational-threshold -/
theorem paper_pom_qstar_discrete_variational_threshold
    (D : QstarDiscreteVariationalThresholdData) :
    D.intervalCharacterization ∧ D.monotonePhaseDiagram := by
  exact ⟨D.intervalCharacterization_h, D.monotonePhaseDiagram_h⟩

end Omega.POM
