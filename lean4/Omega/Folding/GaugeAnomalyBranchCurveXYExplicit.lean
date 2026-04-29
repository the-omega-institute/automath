import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyBranchpointRationalReduction

namespace Omega.Folding

/-- The explicit elimination polynomial cutting out the branch curve in the monomial coordinates
`X = t * u`, `Y = u^3`. -/
def gaugeAnomalyBranchCurveR (X Y : ℚ) : ℚ :=
  20 * X ^ 5 - 8 * X ^ 4 * Y - 120 * X ^ 4 + 4 * X ^ 3 * Y ^ 2 + 236 * X ^ 3 * Y +
    220 * X ^ 3 - 239 * X ^ 2 * Y ^ 2 - 164 * X ^ 2 * Y - 120 * X ^ 2 + 90 * X * Y ^ 3 -
    70 * X * Y ^ 2 - 108 * X * Y + 20 * X - 27 * Y ^ 4 - 22 * Y ^ 3 + 5 * Y ^ 2

/-- Paper-facing wrapper for the explicit branch curve equation: the existing rational branchpoint
parametrization is preserved, and substituting it into the elimination polynomial gives an
identically vanishing relation.
    prop:fold-gauge-anomaly-branch-curve-XY-explicit -/
def gaugeAnomalyBranchCurveXYExplicit : Prop :=
  (∀ μ : ℚ, gaugeAnomalyBranchX μ = μ ^ 2 * (3 * μ ^ 2 - 2 * μ - 1) / (μ ^ 2 + 1)) ∧
    (∀ μ : ℚ, gaugeAnomalyBranchY μ = -2 * μ * (μ ^ 2 - μ - 1) ^ 2 / (μ ^ 2 + 1)) ∧
    ∀ μ : ℚ, gaugeAnomalyBranchCurveR (gaugeAnomalyBranchX μ) (gaugeAnomalyBranchY μ) = 0

theorem paper_fold_gauge_anomaly_branch_curve_xy_explicit : gaugeAnomalyBranchCurveXYExplicit := by
  refine ⟨?_, ?_, ?_⟩
  · intro μ
    rfl
  · intro μ
    rfl
  · intro μ
    have hμ : μ ^ 2 + 1 ≠ 0 := by
      nlinarith [sq_nonneg μ]
    unfold gaugeAnomalyBranchCurveR gaugeAnomalyBranchX gaugeAnomalyBranchY
    field_simp [hμ]
    ring_nf

end Omega.Folding
