import Omega.Folding.Rewrite

namespace Omega.Folding

open Omega.Rewrite

/-- Paper label: `cor:foldm-order-indep`. -/
theorem paper_foldm_order_indep {m : ℕ} (w : Word m) :
    Fold w = normalPrefix (iota w) m := by
  exact (normalPrefix_iota_eq_Fold w).symm

end Omega.Folding
