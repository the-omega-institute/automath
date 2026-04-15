namespace Omega.POM

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the microcanonical band bounds theorem in
    `2026_projection_ontological_mathematics_core_tams`.
    thm:microcanonical-bands -/
theorem paper_projection_microcanonical_band_bounds
    (gibbsSelection bandConcentration bandCardinalityBounds bandProbabilityBounds : Prop)
    (hSelection : gibbsSelection)
    (hConcentration : gibbsSelection → bandConcentration)
    (hCardinality : bandConcentration → bandCardinalityBounds)
    (hProbability : bandConcentration → bandProbabilityBounds) :
    gibbsSelection ∧ bandConcentration ∧ bandCardinalityBounds ∧ bandProbabilityBounds := by
  have hBand : bandConcentration := hConcentration hSelection
  exact ⟨hSelection, hBand, hCardinality hBand, hProbability hBand⟩

end Omega.POM
