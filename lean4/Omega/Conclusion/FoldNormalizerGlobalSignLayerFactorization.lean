import Omega.OperatorAlgebra.FoldGlobalSignUniqueDecomposition

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-fold-normalizer-global-sign-layer-factorization`. The conclusion
chapter uses the same visible and hidden sign-character products as the operator-algebra normalizer
factorization. -/
theorem paper_conclusion_fold_normalizer_global_sign_layer_factorization {m : Nat}
    (d : Fin m → Nat) :
    ∀ tau : Omega.OperatorAlgebra.FoldFiberNormalizer d,
      Omega.OperatorAlgebra.globalSign tau =
        Omega.OperatorAlgebra.visibleCharacterProduct d tau *
          Omega.OperatorAlgebra.fiberCharacterProduct d tau := by
  exact Omega.OperatorAlgebra.paper_op_algebra_fold_global_sign_unique_decomposition d

end Omega.Conclusion
