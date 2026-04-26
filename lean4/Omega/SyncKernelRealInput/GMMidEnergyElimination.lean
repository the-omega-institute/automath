import Mathlib.Tactic
import Omega.SyncKernelRealInput.GMContinuousMajorArcControl
import Omega.SyncKernelRealInput.GMEnergyWindowSaving
import Omega.SyncKernelRealInput.GMRelativeGapAfterObstruction

namespace Omega.SyncKernelRealInput

/-- Concrete input package for the mid-energy elimination step: a continuous major-arc estimate,
the obstruction-removal relative gap package, and the rational energy-window exponent. -/
structure gm_mid_energy_elimination_data where
  majorArc : gm_continuous_major_arc_control_data
  relativeGap : gm_relative_gap_after_obstruction_data
  theta : ℚ

namespace gm_mid_energy_elimination_data

/-- The composed paper-facing conclusion: positive major-arc constants, a positive extracted
saving exponent, obstruction-removal improvement, and the audited energy-window identity. -/
def statement (D : gm_mid_energy_elimination_data) : Prop :=
  ∃ c1 c2 eps : ℝ,
    0 < c1 ∧
      0 < c2 ∧
        0 < eps ∧
          (∀ m q : ℕ, ∀ beta : ℝ,
            D.majorArc.normalized_sum m q beta ≤
              Real.exp (-c1 * (m : ℝ) / D.majorArc.pisano q) +
                Real.exp (-c2 * (m : ℝ) * beta ^ 2 * D.majorArc.variance m q)) ∧
            D.relativeGap.nonresonant_twist_gap ∧
              D.relativeGap.relative_affine_residual_improvement ∧
                (6 / 5 : ℚ) * (1 - D.theta / 2) + (1 + D.theta / 2) =
                  11 / 5 - D.theta / 10

end gm_mid_energy_elimination_data

/-- Paper label: `thm:gm-mid-energy-elimination`. The major-arc wrapper supplies the positive
constants, the obstruction-gap wrapper supplies the post-projection gap and residual improvement,
and the energy-window wrapper supplies the exact rational saving identity. -/
theorem paper_gm_mid_energy_elimination (D : gm_mid_energy_elimination_data) : D.statement := by
  rcases paper_gm_continuous_major_arc_control D.majorArc with
    ⟨c1, c2, hc1, hc2, hmajor⟩
  rcases paper_gm_relative_gap_after_obstruction D.relativeGap with ⟨hgap, himprove⟩
  refine ⟨c1, c2, (1 : ℝ) / 10, hc1, hc2, by norm_num, hmajor, hgap, himprove, ?_⟩
  exact paper_gm_energy_window_saving D.theta

end Omega.SyncKernelRealInput
