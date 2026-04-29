namespace Omega.Zeta

/-- Paper label: `thm:xi-poisson-coarsegraining-first-mismatch-kl`. -/
theorem paper_xi_poisson_coarsegraining_first_mismatch_kl
    (momentMatching taylorMainTerm derivativeEnergy klQuadraticExpansion asymptoticClaim : Prop)
    (hmom : momentMatching) (htaylor : momentMatching -> taylorMainTerm)
    (henergy : derivativeEnergy)
    (hkl : taylorMainTerm -> derivativeEnergy -> klQuadraticExpansion)
    (hasymp : klQuadraticExpansion -> asymptoticClaim) :
    asymptoticClaim := by
  exact hasymp (hkl (htaylor hmom) henergy)

end Omega.Zeta
