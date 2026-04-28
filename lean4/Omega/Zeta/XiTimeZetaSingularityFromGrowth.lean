namespace Omega.Zeta

/-- Paper label: `thm:xi-time-zeta-singularity-from-growth`. -/
theorem paper_xi_time_zeta_singularity_from_growth
    (spectralDimension convergenceHalfPlane exponentialGrowth volumeEntropyNormalized
      heatTraceExpansion poleResidues : Prop)
    (hConv : spectralDimension -> convergenceHalfPlane)
    (hGrowth : exponentialGrowth -> volumeEntropyNormalized)
    (hHeat : heatTraceExpansion -> poleResidues) :
    spectralDimension ->
      exponentialGrowth -> heatTraceExpansion -> convergenceHalfPlane ∧
        volumeEntropyNormalized ∧ poleResidues := by
  intro hSpectral hExponential hHeatTrace
  exact ⟨hConv hSpectral, hGrowth hExponential, hHeat hHeatTrace⟩

end Omega.Zeta
