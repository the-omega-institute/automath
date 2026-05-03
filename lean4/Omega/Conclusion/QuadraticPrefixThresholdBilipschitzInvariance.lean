import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

namespace Omega.Conclusion

noncomputable section

/-- Concrete parameters for the quadratic prefix threshold under a bi-Lipschitz coordinate
change. -/
structure conclusion_quadratic_prefix_threshold_bilipschitz_invariance_data where
  logHeight : ℝ
  prefixBits : ℝ
  residualBits : ℝ
  bilipschitzConstant : ℝ

/-- Original quadratic-prefix lower-bound scale. -/
def conclusion_quadratic_prefix_threshold_bilipschitz_invariance_original_threshold
    (D : conclusion_quadratic_prefix_threshold_bilipschitz_invariance_data) : ℝ :=
  2 * D.logHeight + Real.log (D.logHeight + 1)

/-- The `O_phi(1)` distortion constant coming from the bi-Lipschitz chart. -/
def conclusion_quadratic_prefix_threshold_bilipschitz_invariance_distortion_constant
    (D : conclusion_quadratic_prefix_threshold_bilipschitz_invariance_data) : ℝ :=
  |D.bilipschitzConstant|

/-- Threshold after a bi-Lipschitz coordinate change. -/
def conclusion_quadratic_prefix_threshold_bilipschitz_invariance_distorted_threshold
    (D : conclusion_quadratic_prefix_threshold_bilipschitz_invariance_data) : ℝ :=
  conclusion_quadratic_prefix_threshold_bilipschitz_invariance_original_threshold D +
    conclusion_quadratic_prefix_threshold_bilipschitz_invariance_distortion_constant D

/-- Available prefix-plus-residual bit budget. -/
def conclusion_quadratic_prefix_threshold_bilipschitz_invariance_budget
    (D : conclusion_quadratic_prefix_threshold_bilipschitz_invariance_data) : ℝ :=
  D.prefixBits + D.residualBits

namespace conclusion_quadratic_prefix_threshold_bilipschitz_invariance_data

/-- A lower bound transfers through the chart after adding the chart-dependent constant. -/
def threshold_invariant
    (D : conclusion_quadratic_prefix_threshold_bilipschitz_invariance_data) : Prop :=
  ∀ B : ℝ,
    conclusion_quadratic_prefix_threshold_bilipschitz_invariance_original_threshold D ≤ B →
      conclusion_quadratic_prefix_threshold_bilipschitz_invariance_distorted_threshold D ≤
        B + conclusion_quadratic_prefix_threshold_bilipschitz_invariance_distortion_constant D

end conclusion_quadratic_prefix_threshold_bilipschitz_invariance_data

/-- Paper label:
`prop:conclusion-quadratic-prefix-threshold-bilipschitz-invariance`. -/
theorem paper_conclusion_quadratic_prefix_threshold_bilipschitz_invariance
    (D : conclusion_quadratic_prefix_threshold_bilipschitz_invariance_data) :
    D.threshold_invariant := by
  intro B hB
  rw [conclusion_quadratic_prefix_threshold_bilipschitz_invariance_distorted_threshold]
  linarith

end

end Omega.Conclusion
