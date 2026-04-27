import Omega.OperatorAlgebra.FoldGroupoidMatrixUnitAutNormalizer

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-fold-groupoid-matrixunit-normalizer`.

The conclusion-level normalizer statement is the packaged operator-algebra matrix-unit
normalizer theorem. -/
theorem paper_conclusion_fold_groupoid_matrixunit_normalizer
    (D : Omega.OperatorAlgebra.FoldGroupoidMatrixUnitAutNormalizerData) :
    D.forwardMapWellDefined ∧ D.inverseMapWellDefined ∧ D.normalizerEquivMatrixUnitAut := by
  exact Omega.OperatorAlgebra.paper_op_algebra_fold_groupoid_matrix_unit_aut_normalizer D

end Omega.Conclusion
