import Omega.Zeta.CLTSpectral

namespace Omega.Zeta

/-- Spectral-gap CLT package together with the same-hypothesis nonzero-frequency decay.
    thm:conclusion63-clt-spectral -/
theorem paper_conclusion63_clt_spectral
    (spectralRadiusGap analyticPerturbation nonCoboundary positiveVariance centralLimitTheorem
      highFrequencyDecay : Prop)
    (hGap : spectralRadiusGap) (hPerturb : analyticPerturbation)
    (hVariance :
      spectralRadiusGap → analyticPerturbation → nonCoboundary → positiveVariance)
    (hCLT : positiveVariance → centralLimitTheorem)
    (hDecay : spectralRadiusGap → analyticPerturbation → highFrequencyDecay) :
    nonCoboundary → positiveVariance ∧ centralLimitTheorem ∧ highFrequencyDecay := by
  intro hNonCoboundary
  rcases
      paper_fredholm_witt_clt_spectral spectralRadiusGap analyticPerturbation nonCoboundary
        positiveVariance centralLimitTheorem hGap hPerturb hVariance hCLT hNonCoboundary with
    ⟨hPositiveVariance, hCentralLimitTheorem⟩
  exact ⟨hPositiveVariance, hCentralLimitTheorem, hDecay hGap hPerturb⟩

end Omega.Zeta
