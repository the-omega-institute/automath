import Omega.OperatorAlgebra.FoldFiberNormalizerWreath

namespace Omega.OperatorAlgebra

/-- Paper label: `cor:op-algebra-fold-group-orders`. -/
theorem paper_op_algebra_fold_group_orders {m : Nat} (d : Fin m → Nat) :
    Fintype.card (HiddenFiberAutomorphisms d) = ∏ x, Nat.factorial (d x) ∧
      Fintype.card (FoldFiberNormalizer d) =
        Fintype.card (CompatibleVisiblePerm d) * ∏ x, Nat.factorial (d x) := by
  simpa using (paper_op_algebra_fold_fiber_normalizer_wreath (d := d)).2.2.2.2

end Omega.OperatorAlgebra
