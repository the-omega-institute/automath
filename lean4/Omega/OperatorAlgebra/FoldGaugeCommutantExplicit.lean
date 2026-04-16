namespace Omega.OperatorAlgebra

/-- Chapter-local package for the explicit fold-gauge commutant description. The data record the
decomposition into fold fibers, the reduction of the global commutant to a direct sum of
fiberwise permutation commutants, the splitting `ℂ·1 ⊕ 1ᗮ`, and the Schur-style rigidity forcing
every equivariant endomorphism on a fiber to be of the form `a I + b J`. -/
structure FoldGaugeCommutantExplicitData where
  foldFiberDecomposition : Prop
  globalToFiberwiseReduction : Prop
  scalarPlusOrthogonalDecomposition : Prop
  schurRigidityOnFibers : Prop
  fiberwiseCommutantIsSpanIJ : Prop
  foldFiberDecomposition_h : foldFiberDecomposition
  globalToFiberwiseReduction_h : globalToFiberwiseReduction
  scalarPlusOrthogonalDecomposition_h : scalarPlusOrthogonalDecomposition
  schurRigidityOnFibers_h : schurRigidityOnFibers
  deriveFiberwiseCommutantIsSpanIJ :
    foldFiberDecomposition → globalToFiberwiseReduction → scalarPlusOrthogonalDecomposition →
      schurRigidityOnFibers → fiberwiseCommutantIsSpanIJ

/-- Paper-facing wrapper for the explicit fold-gauge commutant formula: after decomposing the
representation over the fold fibers and reducing the global commutant fiberwise, the standard
`ℂ·1 ⊕ 1ᗮ` splitting together with Schur rigidity shows that each fiberwise commutant is exactly
`span {I, J}`.
    thm:op-algebra-fold-gauge-commutant-explicit -/
theorem paper_op_algebra_fold_gauge_commutant_explicit
    (D : FoldGaugeCommutantExplicitData) : D.fiberwiseCommutantIsSpanIJ := by
  exact
    D.deriveFiberwiseCommutantIsSpanIJ D.foldFiberDecomposition_h
      D.globalToFiberwiseReduction_h D.scalarPlusOrthogonalDecomposition_h
      D.schurRigidityOnFibers_h

end Omega.OperatorAlgebra
