namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the spectral-gap central limit theorem in
    `2026_fredholm_witt_cyclic_block_spectral_rigidity_symbolic_zeta`.
    thm:clt-spectral -/
theorem paper_fredholm_witt_clt_spectral
    (spectralRadiusGap analyticPerturbation nonCoboundary positiveVariance centralLimitTheorem :
      Prop)
    (hGap : spectralRadiusGap)
    (hPerturb : analyticPerturbation)
    (hVariance :
      spectralRadiusGap → analyticPerturbation → nonCoboundary → positiveVariance)
    (hCLT : positiveVariance → centralLimitTheorem) :
    nonCoboundary → positiveVariance ∧ centralLimitTheorem := by
  intro hNonCoboundary
  have hPositiveVariance : positiveVariance := hVariance hGap hPerturb hNonCoboundary
  exact ⟨hPositiveVariance, hCLT hPositiveVariance⟩

end Omega.Zeta
