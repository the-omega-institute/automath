namespace Omega.OperatorAlgebra

/-- Chapter-local package for the replication-centralizer dimension corollary. The data record
the restricted-Bell closed form for the dimensions and the extraction of the even part of the
orbit exponential generating function. -/
structure ReplicationCentralizerDimensionEgfData where
  orbitAlgebraDimensionInput : Prop
  exponentialGeneratingFunctionInput : Prop
  dimensionClosedForm : Prop
  evenExponentialGeneratingFunction : Prop
  orbitAlgebraDimensionInput_h : orbitAlgebraDimensionInput
  exponentialGeneratingFunctionInput_h : exponentialGeneratingFunctionInput
  deriveDimensionClosedForm :
    orbitAlgebraDimensionInput → dimensionClosedForm
  deriveEvenExponentialGeneratingFunction :
    dimensionClosedForm → exponentialGeneratingFunctionInput →
      evenExponentialGeneratingFunction

/-- Paper-facing wrapper for the centralizer-dimension corollary: the orbit-algebra theorem
gives the restricted-Bell closed form, and the orbit generating function yields the even
exponential generating function.
    cor:op-algebra-replication-centralizer-dimension-egf -/
theorem paper_op_algebra_replication_centralizer_dimension_egf
    (D : ReplicationCentralizerDimensionEgfData) :
    D.dimensionClosedForm ∧ D.evenExponentialGeneratingFunction := by
  have hClosed : D.dimensionClosedForm :=
    D.deriveDimensionClosedForm D.orbitAlgebraDimensionInput_h
  exact ⟨hClosed,
    D.deriveEvenExponentialGeneratingFunction hClosed D.exponentialGeneratingFunctionInput_h⟩

end Omega.OperatorAlgebra
