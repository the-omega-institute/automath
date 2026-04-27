import Omega.Folding.FoldGaugeAnomalyP10P9LinearDisjointness

namespace Omega.Folding

/-- Concrete data for the paper-facing lowercase `P10/P9` linear-disjointness wrapper. -/
abbrev fold_gauge_anomaly_p10_p9_linear_disjointness_data :=
  FoldGaugeAnomalyP10P9Data

/-- The lowercase statement mirrors the already audited `P10/P9` direct-product package. -/
def fold_gauge_anomaly_p10_p9_linear_disjointness_statement
    (D : fold_gauge_anomaly_p10_p9_linear_disjointness_data) : Prop :=
  D.intersectionIsBase ∧
    D.galoisGroupIsDirectProduct ∧
    D.compositumDegree = Nat.factorial 10 * Nat.factorial 9

/-- Paper label: `thm:fold-gauge-anomaly-P10-P9-linear-disjointness`. -/
theorem paper_fold_gauge_anomaly_p10_p9_linear_disjointness
    (D : fold_gauge_anomaly_p10_p9_linear_disjointness_data) :
    fold_gauge_anomaly_p10_p9_linear_disjointness_statement D := by
  simpa [fold_gauge_anomaly_p10_p9_linear_disjointness_statement] using
    paper_fold_gauge_anomaly_P10_P9_linear_disjointness D

end Omega.Folding
