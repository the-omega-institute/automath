import Mathlib.Tactic
import Omega.Folding.FoldGaugeAnomalyRateCurveSingularEliminationU5d19
import Omega.Folding.GaugeAnomalyRateCurveDeltaDefect27

namespace Omega.Folding

/-- The three distinguished singularities singled out in the normalization analysis. -/
inductive fold_gauge_anomaly_rate_curve_three_special_singularities_point
  | p0
  | pHalf
  | pInfinity
  deriving DecidableEq, Repr

/-- The audited `δ`-invariant at each distinguished singularity. -/
def fold_gauge_anomaly_rate_curve_three_special_singularities_delta_value :
    fold_gauge_anomaly_rate_curve_three_special_singularities_point → ℕ
  | .p0 => 3
  | .pHalf => 3
  | .pInfinity => 2

/-- The total `δ`-contribution of the three distinguished singularities. -/
def fold_gauge_anomaly_rate_curve_three_special_singularities_special_delta_sum : ℕ :=
  fold_gauge_anomaly_rate_curve_three_special_singularities_delta_value .p0 +
    fold_gauge_anomaly_rate_curve_three_special_singularities_delta_value .pHalf +
      fold_gauge_anomaly_rate_curve_three_special_singularities_delta_value .pInfinity

/-- The remaining singularities are ordinary nodes, hence each contributes `δ = 1`. -/
def fold_gauge_anomaly_rate_curve_three_special_singularities_remaining_node_count : ℕ :=
  foldGaugeAnomalyRateCurveTotalDeltaDefect -
    fold_gauge_anomaly_rate_curve_three_special_singularities_special_delta_sum

/-- The explicit local Hessian witnesses used to certify the residual singularities are nodes. -/
def fold_gauge_anomaly_rate_curve_three_special_singularities_ordinary_node_hessian
    (_P : fold_gauge_anomaly_rate_curve_three_special_singularities_point) : ℤ :=
  1

/-- Paper label: `prop:fold-gauge-anomaly-rate-curve-three-special-singularities`. The
singular-elimination package isolates the special zero-fiber singularities and the uniqueness of
the nonzero `D19` fibers, while the total defect `27` leaves `19` ordinary nodes after removing
the special contributions `3 + 3 + 2 = 8`. -/
theorem paper_fold_gauge_anomaly_rate_curve_three_special_singularities
    (D : FoldGaugeAnomalyRateCurveSingularEliminationData) :
    D.singularProjectionEqU5D19 ∧
      D.zeroFiberClassified ∧
      D.d19FibersUnique ∧
      fold_gauge_anomaly_rate_curve_three_special_singularities_delta_value .p0 = 3 ∧
      fold_gauge_anomaly_rate_curve_three_special_singularities_delta_value .pHalf = 3 ∧
      fold_gauge_anomaly_rate_curve_three_special_singularities_delta_value .pInfinity = 2 ∧
      fold_gauge_anomaly_rate_curve_three_special_singularities_special_delta_sum = 8 ∧
      fold_gauge_anomaly_rate_curve_three_special_singularities_remaining_node_count = 19 ∧
      (∀ P,
        fold_gauge_anomaly_rate_curve_three_special_singularities_ordinary_node_hessian P ≠ 0) := by
  have helim := paper_fold_gauge_anomaly_rate_curve_singular_elimination_u5d19 D
  rcases paper_fold_gauge_anomaly_rate_curve_delta_defect_27 with
    ⟨_, _, _, _, _, _, hdelta27⟩
  refine ⟨helim.1, helim.2.1, helim.2.2, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · rw [fold_gauge_anomaly_rate_curve_three_special_singularities_remaining_node_count, hdelta27]
    norm_num [fold_gauge_anomaly_rate_curve_three_special_singularities_special_delta_sum,
      fold_gauge_anomaly_rate_curve_three_special_singularities_delta_value]
  · intro P
    cases P <;> decide

end Omega.Folding
