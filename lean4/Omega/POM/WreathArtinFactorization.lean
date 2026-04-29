namespace Omega.POM

/-- Paper label: `cor:pom-wreath-artin-factorization`. -/
theorem paper_pom_wreath_artin_factorization
    (momentWreathLift regularRepresentationArtinSplit liftedZetaFactorization : Prop)
    (hSplit : momentWreathLift → regularRepresentationArtinSplit)
    (hFactor : regularRepresentationArtinSplit → liftedZetaFactorization) :
    momentWreathLift → regularRepresentationArtinSplit ∧ liftedZetaFactorization := by
  intro hMoment
  refine ⟨hSplit hMoment, ?_⟩
  exact hFactor (hSplit hMoment)

end Omega.POM
