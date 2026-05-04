namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-realinput40-mirror-perron-sqrt-slowdown`. -/
theorem paper_conclusion_realinput40_mirror_perron_sqrt_slowdown
    (puiseux mirrorDominates gapLaw relaxationLaw noPowerSaving : Prop)
    (hgap : puiseux -> mirrorDominates -> gapLaw)
    (htau : gapLaw -> relaxationLaw)
    (hpow : puiseux -> mirrorDominates -> noPowerSaving) :
    puiseux -> mirrorDominates -> gapLaw ∧ relaxationLaw ∧ noPowerSaving := by
  intro hPuiseux hMirrorDominates
  have hGapLaw : gapLaw := hgap hPuiseux hMirrorDominates
  have hRelaxationLaw : relaxationLaw := htau hGapLaw
  have hNoPowerSaving : noPowerSaving := hpow hPuiseux hMirrorDominates
  exact ⟨hGapLaw, hRelaxationLaw, hNoPowerSaving⟩

end Omega.Conclusion
