import Omega.Folding.FiberArithmeticProperties

namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Resolution-folding publication wrapper for the order-independent fold corollary.
    cor:fold-order-independent -/
theorem paper_resolution_folding_fold_order_independent (m : ℕ) :
    (∀ w : Omega.Word m, Omega.Fold (Omega.Fold w).1 = Omega.Fold w) ∧
      (∀ w : Omega.Word m, Omega.No11 (Omega.Fold w).1) ∧
      Function.Surjective (Omega.Fold (m := m)) :=
  Omega.X.paper_fold_order_independent (m := m)

end Omega.Folding
