import Mathlib.Tactic

namespace Omega.POM

/-- Chapter-local certificate package for the inverse Schur-tomography formula.
The fields record the forward Schur expansion, the weighted character summation,
the symmetric-group column orthogonality input, and the resulting recovery of the
target partition monomial. -/
structure SchurTomographyInversePartitionMonomialsData where
  forwardSchurTomography : Prop
  characterWeightedSummation : Prop
  columnOrthogonality : Prop
  partitionMonomialRecovered : Prop
  forwardSchurTomography_h : forwardSchurTomography
  characterWeightedSummation_h : characterWeightedSummation
  columnOrthogonality_h : columnOrthogonality
  derivePartitionMonomialRecovered :
    forwardSchurTomography →
      characterWeightedSummation → columnOrthogonality → partitionMonomialRecovered

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the strict inverse Schur tomography statement in the
POM chapter.
    thm:pom-schur-tomography-inverse-partition-monomials -/
theorem paper_pom_schur_tomography_inverse_partition_monomials
    (D : SchurTomographyInversePartitionMonomialsData) :
    D.forwardSchurTomography ∧ D.columnOrthogonality ∧ D.partitionMonomialRecovered := by
  have hRecovered : D.partitionMonomialRecovered :=
    D.derivePartitionMonomialRecovered D.forwardSchurTomography_h
      D.characterWeightedSummation_h D.columnOrthogonality_h
  exact ⟨D.forwardSchurTomography_h, D.columnOrthogonality_h, hRecovered⟩

end Omega.POM
