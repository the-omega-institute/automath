import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Perm

namespace Omega.Folding

/-- The finite Chebotarev event on `S₁₀ × S₁₉` has product cardinality.
    cor:fold-gauge-anomaly-P10-H-chebotarev-product-law -/
theorem paper_fold_gauge_anomaly_P10_H_chebotarev_product_law
    (C10 : Finset (Equiv.Perm (Fin 10))) (C19 : Finset (Equiv.Perm (Fin 19))) :
    (C10.product C19).card = C10.card * C19.card := by
  simp [Finset.card_product]

end Omega.Folding
