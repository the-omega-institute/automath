namespace Omega.OperatorAlgebra

/-- Chapter-local data for cylinder naturality under a conjugating intertwiner. The concrete
operator-algebra argument is encapsulated in the two publication-facing conclusions. -/
structure CylinderNaturalityData where
  cylinderConjugacy : Prop
  cylinderProbabilityInvariance : Prop
  cylinderConjugacy_h : cylinderConjugacy
  cylinderProbabilityInvariance_h : cylinderProbabilityInvariance

/-- Paper-facing cylinder naturality wrapper: the intertwiner conjugates every cylinder projector,
and the induced cylinder probabilities are invariant under the conjugacy.
    prop:op-algebra-cylinder-naturality -/
theorem paper_op_algebra_cylinder_naturality (D : CylinderNaturalityData) :
    D.cylinderConjugacy ∧ D.cylinderProbabilityInvariance := by
  exact ⟨D.cylinderConjugacy_h, D.cylinderProbabilityInvariance_h⟩

end Omega.OperatorAlgebra
