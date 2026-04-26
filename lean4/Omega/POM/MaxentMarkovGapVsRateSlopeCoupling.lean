import Mathlib.Tactic
import Omega.POM.MaxentMarkovLaguerreSecularSpectrum

namespace Omega.POM

open scoped BigOperators

/-- Paper label: `cor:pom-maxent-markov-gap-vs-rate-slope-coupling`.

In the one-pole model the spectral-gap slope is `κ`, the rate-slope coefficient is `κ⁻¹`, and
normalizing by the endpoint scale `δ / C₁/₂(w)` leaves the exact coupling constant `κ C₁/₂(w)`. -/
theorem paper_pom_maxent_markov_gap_vs_rate_slope_coupling
    (D : MaxentMarkovLaguerreSecularSpectrumData) {k : ℕ} (w : Fin k → ℝ)
    (hC : ((∑ i, Real.sqrt (w i)) ^ 2 - 1) ≠ 0) :
    D.kappa * (1 / D.kappa) = 1 ∧
      ∀ δ : ℝ, δ ≠ 0 →
        (1 - (1 - D.kappa * δ)) / (δ / (((∑ i, Real.sqrt (w i)) ^ 2 - 1))) =
          D.kappa * (((∑ i, Real.sqrt (w i)) ^ 2 - 1)) := by
  refine ⟨?_, ?_⟩
  · have hk : D.kappa ≠ 0 := ne_of_gt D.kappa_pos
    field_simp [hk]
  · intro δ hδ
    field_simp [hδ, hC]
    ring

end Omega.POM
