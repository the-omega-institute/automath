theorem paper_pom_pressure_delay_lower_bound
    (hardeningMixingBound exponentialReliability linearDelayBound : Prop)
    (hMix : hardeningMixingBound)
    (hReliability : exponentialReliability)
    (hLinear : hardeningMixingBound → exponentialReliability → linearDelayBound) :
    hardeningMixingBound ∧ exponentialReliability ∧ linearDelayBound := by
  exact ⟨hMix, hReliability, hLinear hMix hReliability⟩
