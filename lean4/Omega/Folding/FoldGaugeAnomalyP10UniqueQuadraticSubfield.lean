import Mathlib.Tactic
import Omega.Folding.FoldGaugeAnomalyP10GaloisDiscriminant

namespace Omega.Folding

open FoldGaugeAnomalyP10GaloisDiscriminantData

/-- Paper label: `cor:fold-gauge-anomaly-p10-unique-quadratic-subfield`. The `S10`
Galois/discriminant package already records the unique quadratic sign subfield, and the
squarefree discriminant kernel normalizes to `66269989`. -/
theorem paper_fold_gauge_anomaly_p10_unique_quadratic_subfield
    (D : FoldGaugeAnomalyP10GaloisDiscriminantData) :
    D.galois_group_is_S10 ∧ D.unique_quadratic_subfield ∧
      D.fold_gauge_anomaly_p10_galois_discriminant_squarefree_kernel = 66269989 := by
  rcases paper_fold_gauge_anomaly_p10_galois_discriminant D with ⟨_, hgalois, _, hquad, _⟩
  refine ⟨hgalois, hquad, ?_⟩
  calc
    D.fold_gauge_anomaly_p10_galois_discriminant_squarefree_kernel = 1931 * 34319 := hquad.2
    _ = 66269989 := by norm_num

end Omega.Folding
