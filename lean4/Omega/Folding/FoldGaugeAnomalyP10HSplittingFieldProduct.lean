import Omega.Folding.FoldGaugeAnomalyP10HLinearDisjointness

namespace Omega.Folding

/-- Paper label: `cor:fold-gauge-anomaly-P10H-splitting-field-product`.
The audited `P10/H` linear-disjointness package gives the direct-product Galois description, and
the compositum degree is the product of the two splitting-field degrees. -/
theorem paper_fold_gauge_anomaly_P10H_splitting_field_product :
    foldGaugeAnomalyP10HDirectProductGalois ∧
      foldGaugeAnomalyP10HCompositumDegree = Nat.factorial 10 * Nat.factorial 19 := by
  rcases paper_fold_gauge_anomaly_P10_H_linear_disjointness with
    ⟨_, _, _, hdirect, hdegree⟩
  exact ⟨hdirect, hdegree⟩

/-- Paper label: `cor:fold-gauge-anomaly-P10H-splitting-field-product`. -/
theorem paper_fold_gauge_anomaly_p10h_splitting_field_product :
    foldGaugeAnomalyP10HDirectProductGalois ∧
      foldGaugeAnomalyP10HCompositumDegree = Nat.factorial 10 * Nat.factorial 19 := by
  exact paper_fold_gauge_anomaly_P10H_splitting_field_product

end Omega.Folding
