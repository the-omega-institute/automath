namespace Omega.Zeta

/-- Paper label: `thm:xi-reversekl-poisson-extremal-gap-fourier-stability`. -/
theorem paper_xi_reversekl_poisson_extremal_gap_fourier_stability
    (poissonBounds strongConvexJensen parsevalGap pointMassRigidity : Prop)
    (hbounds : poissonBounds)
    (hjensen : poissonBounds -> strongConvexJensen)
    (hparseval : strongConvexJensen -> parsevalGap)
    (hrigid : parsevalGap -> pointMassRigidity) :
    parsevalGap ∧ pointMassRigidity := by
  have hJensen : strongConvexJensen := hjensen hbounds
  have hGap : parsevalGap := hparseval hJensen
  exact ⟨hGap, hrigid hGap⟩

end Omega.Zeta
