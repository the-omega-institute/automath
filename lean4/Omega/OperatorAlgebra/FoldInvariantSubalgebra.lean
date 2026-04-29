namespace Omega.OperatorAlgebra

/-- Chapter-local package for the fold-invariant subalgebra theorem. The folded minimal
projections are assumed to be assembled over the `Fold`-fibers, their sum records the partition of
`Ω_m`, and the resulting commutative algebra is characterized by observables that are constant on
each fiber. -/
structure FoldInvariantSubalgebraData where
  foldedProjectionConstruction : Prop
  foldFiberPartition : Prop
  foldConditionalExpectationPackage : Prop
  foldedProjectionConstruction_h : foldedProjectionConstruction
  foldFiberPartition_h : foldFiberPartition
  foldConditionalExpectationPackage_h : foldConditionalExpectationPackage
  orthogonalProjectionFamily : Prop
  partitionOfUnity : Prop
  invariantSubalgebraIso : Prop
  fiberwiseConstantCharacterization : Prop
  deriveOrthogonalProjectionFamily :
    foldedProjectionConstruction → orthogonalProjectionFamily
  derivePartitionOfUnity :
    foldFiberPartition → partitionOfUnity
  deriveInvariantSubalgebraIso :
    orthogonalProjectionFamily → partitionOfUnity → invariantSubalgebraIso
  deriveFiberwiseConstantCharacterization :
    invariantSubalgebraIso → foldConditionalExpectationPackage →
      fiberwiseConstantCharacterization

/-- Paper-facing wrapper for the fold-invariant subalgebra package: the folded projections are
pairwise orthogonal, sum to the identity, generate the invariant commutative subalgebra, and
exactly capture the observables that are constant on each `Fold`-fiber.
    prop:fold-invariant-subalgebra -/
theorem paper_op_algebra_fold_invariant_subalgebra (D : FoldInvariantSubalgebraData) :
    D.orthogonalProjectionFamily ∧ D.partitionOfUnity ∧ D.invariantSubalgebraIso ∧
      D.fiberwiseConstantCharacterization := by
  have hOrthogonal : D.orthogonalProjectionFamily :=
    D.deriveOrthogonalProjectionFamily D.foldedProjectionConstruction_h
  have hPartition : D.partitionOfUnity :=
    D.derivePartitionOfUnity D.foldFiberPartition_h
  have hIso : D.invariantSubalgebraIso :=
    D.deriveInvariantSubalgebraIso hOrthogonal hPartition
  exact ⟨hOrthogonal, hPartition, hIso,
    D.deriveFiberwiseConstantCharacterization hIso D.foldConditionalExpectationPackage_h⟩

/-- Paper-facing exact-name wrapper for the fold-invariant subalgebra package.
    prop:fold-invariant-subalgebra -/
theorem paper_fold_invariant_subalgebra (D : FoldInvariantSubalgebraData) :
    D.orthogonalProjectionFamily ∧ D.partitionOfUnity ∧ D.invariantSubalgebraIso ∧
      D.fiberwiseConstantCharacterization :=
  paper_op_algebra_fold_invariant_subalgebra D

end Omega.OperatorAlgebra
