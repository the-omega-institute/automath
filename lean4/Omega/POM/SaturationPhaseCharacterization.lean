import Mathlib

namespace Omega.POM

/-- Paper label: `prop:pom-saturation-phase-characterization`. -/
theorem paper_pom_saturation_phase_characterization
    (saturation concentration rateZero : Prop)
    (hSatToConc : saturation → concentration)
    (hConcToRate : concentration → rateZero)
    (hRateToSat : rateZero → saturation) :
    (saturation ↔ concentration) ∧ (concentration ↔ rateZero) := by
  exact
    ⟨⟨hSatToConc, fun hConc => hRateToSat (hConcToRate hConc)⟩,
      ⟨hConcToRate, fun hRate => hSatToConc (hRateToSat hRate)⟩⟩

end Omega.POM
