namespace Omega.OperatorAlgebra

/-- Chapter-local package for the colored-partition description of the replication centralizer.
The fields encode the operator attached to each admissible colored partition, its equivariance,
the orbit classification of `q`-tuples, the basis theorem for the commutant, and the compatibility
between operator composition and diagram concatenation with loop weights. -/
structure ReplicationCentralizerColoredPartitionOrbitAlgebraData where
  admissibleColoredPartitionOperators : Prop
  qTupleOrbitClassification : Prop
  gmEquivariance : Prop
  commutantBasis : Prop
  compositionMatchesDiagramConcatenation : Prop
  loopWeightCompatibility : Prop
  orbitAlgebraIsomorphicToCentralizer : Prop
  admissibleColoredPartitionOperators_h : admissibleColoredPartitionOperators
  qTupleOrbitClassification_h : qTupleOrbitClassification
  deriveGmEquivariance :
    admissibleColoredPartitionOperators → gmEquivariance
  deriveCommutantBasis :
    gmEquivariance → qTupleOrbitClassification → commutantBasis
  deriveCompositionMatchesDiagramConcatenation :
    admissibleColoredPartitionOperators → compositionMatchesDiagramConcatenation
  deriveLoopWeightCompatibility :
    admissibleColoredPartitionOperators → loopWeightCompatibility
  deriveOrbitAlgebraIsomorphism :
    commutantBasis → compositionMatchesDiagramConcatenation → loopWeightCompatibility →
      orbitAlgebraIsomorphicToCentralizer

/-- Paper-facing wrapper for the identification of the colored partition orbit algebra with the
replication centralizer: admissible colored partitions define equivariant operators, the
orbit-classification argument makes them a basis of the commutant, and composition agrees with
diagram concatenation plus loop weights, yielding the algebra isomorphism.
    thm:op-algebra-replication-centralizer-colored-partition-orbit-algebra -/
theorem paper_op_algebra_replication_centralizer_colored_partition_orbit_algebra
    (D : ReplicationCentralizerColoredPartitionOrbitAlgebraData) :
    D.gmEquivariance ∧ D.commutantBasis ∧ D.compositionMatchesDiagramConcatenation ∧
      D.loopWeightCompatibility ∧ D.orbitAlgebraIsomorphicToCentralizer := by
  have hEquivariance : D.gmEquivariance :=
    D.deriveGmEquivariance D.admissibleColoredPartitionOperators_h
  have hBasis : D.commutantBasis :=
    D.deriveCommutantBasis hEquivariance D.qTupleOrbitClassification_h
  have hComposition : D.compositionMatchesDiagramConcatenation :=
    D.deriveCompositionMatchesDiagramConcatenation D.admissibleColoredPartitionOperators_h
  have hLoops : D.loopWeightCompatibility :=
    D.deriveLoopWeightCompatibility D.admissibleColoredPartitionOperators_h
  exact ⟨hEquivariance, hBasis, hComposition, hLoops,
    D.deriveOrbitAlgebraIsomorphism hBasis hComposition hLoops⟩

end Omega.OperatorAlgebra
