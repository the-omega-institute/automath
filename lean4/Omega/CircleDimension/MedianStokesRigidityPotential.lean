namespace Omega.CircleDimension

/-- Paper-facing wrapper for the median-graph Stokes rigidity package.
    thm:cdim-median-stokes-rigidity-potential -/
theorem paper_cdim_median_stokes_rigidity_potential
    (squareClosed thetaClassConstant exactPotential : Prop)
    (h12 : squareClosed -> thetaClassConstant) (h23 : thetaClassConstant -> exactPotential)
    (h31 : exactPotential -> squareClosed) :
    squareClosed ↔ thetaClassConstant ∧ exactPotential := by
  constructor
  · intro hsq
    refine ⟨h12 hsq, ?_⟩
    exact h23 (h12 hsq)
  · intro hpack
    exact h31 hpack.2

end Omega.CircleDimension
