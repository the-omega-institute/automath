import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- Chapter-local wrapper for the one-way contraction criterion from rough resource geometry to a
symmetric local metric geometry. -/
structure ClassicalContractionData where
  finiteComparableCost : Prop
  symmetricScalarCollapse : Prop
  localResidualAbsorbable : Prop
  budgetAbsorbable : Prop
  contractsToLocalMetricGeometry : Prop
  contractionWitness :
    finiteComparableCost ∧ symmetricScalarCollapse ∧ localResidualAbsorbable ∧ budgetAbsorbable →
      contractsToLocalMetricGeometry

/-- The four contraction hypotheses suffice to collapse the rough resource geometry to a local
metric wrapper.
    prop:typed-address-biaxial-completion-classical-contraction -/
theorem paper_typed_address_biaxial_completion_classical_contraction
    (D : ClassicalContractionData) :
    D.finiteComparableCost ∧
      D.symmetricScalarCollapse ∧
      D.localResidualAbsorbable ∧
      D.budgetAbsorbable →
      D.contractsToLocalMetricGeometry := by
  exact D.contractionWitness

end Omega.TypedAddressBiaxialCompletion
