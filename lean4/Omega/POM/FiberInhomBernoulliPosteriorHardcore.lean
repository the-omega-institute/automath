namespace Omega.POM

/-- Paper label: `cor:pom-fiber-inhom-bernoulli-posterior-hardcore`. -/
theorem paper_pom_fiber_inhom_bernoulli_posterior_hardcore
    (fiberMultiplicativeDecomposition conditionalPosteriorHardcore : Prop)
    (hDecomp : fiberMultiplicativeDecomposition)
    (hHardcore : fiberMultiplicativeDecomposition → conditionalPosteriorHardcore) :
    conditionalPosteriorHardcore := by
  exact hHardcore hDecomp

end Omega.POM
