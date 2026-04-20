import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Perm

namespace Omega.Folding

/-- The finite Chebotarev event on `S₁₀ × S₃` has product cardinality.
    cor:fold-gauge-anomaly-P10-leyang-chebotarev-product-law -/
theorem paper_fold_gauge_anomaly_P10_leyang_chebotarev_product_law
    (C10 : Finset (Equiv.Perm (Fin 10))) (C3 : Finset (Equiv.Perm (Fin 3))) :
    (C10.product C3).card = C10.card * C3.card := by
  simp [Finset.card_product]

end Omega.Folding
