import Mathlib.Tactic
import Omega.Folding.FoldGaugeAnomalyP10LeyangIrreducibleRootSplitDensities

namespace Omega.Folding

/-- Paper-facing wrapper for the audited class sizes and the two displayed rational densities used
in the `P10/H` explicit-density discussion. -/
def fold_gauge_anomaly_p10_h_explicit_densities_statement : Prop :=
  fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_p10_ten_cycle_class_size =
      Nat.factorial 9 ∧
    fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_leyang_transposition_class_size =
      3 ∧
    fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_leyang_identity_class_size = 1 ∧
    fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_irreducible_density =
      (1 : ℚ) / 20 ∧
    fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_split_density =
      (1 : ℚ) / 60

/-- Paper label: `cor:fold-gauge-anomaly-P10-H-explicit-densities`. The already audited
`P10 ×` Lee--Yang `× H` Chebotarev package supplies the class-size normalizations, and the two
displayed densities reduce to rational arithmetic. -/
theorem paper_fold_gauge_anomaly_p10_h_explicit_densities :
    fold_gauge_anomaly_p10_h_explicit_densities_statement := by
  rcases paper_fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities with
    ⟨_, _, hirr, hsplit⟩
  refine ⟨by
    unfold fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_p10_ten_cycle_class_size
    rfl, by
    unfold fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_leyang_transposition_class_size
    norm_num, by
    unfold fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_leyang_identity_class_size
    norm_num, hirr, hsplit⟩

end Omega.Folding
