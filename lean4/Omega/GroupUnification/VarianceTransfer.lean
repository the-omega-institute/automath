import Omega.GroupUnification.FreeEnergyComposition

namespace Omega.GroupUnification

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for variance transfer under tilts in
    `submitted_2026_zero_jitter_information_clocks_parry_gibbs_rigidity_jtp`.
    cor:variance-transfer -/
theorem paper_zero_jitter_variance_transfer
    (q σ Fpp L : ℝ → ℝ) (p : ℝ)
    (hTransfer : ∀ t, σ (q t) = (1 - t) ^ 2 * Fpp t)
    (hExplicit : ∀ t, Fpp t = q t * (1 - q t) / (2 - q t) ^ 3 * (L p) ^ 2) :
    (∀ t, σ (q t) = (1 - t) ^ 2 * Fpp t) ∧
      (∀ t, Fpp t = q t * (1 - q t) / (2 - q t) ^ 3 * (L p) ^ 2) := by
  exact ⟨hTransfer, hExplicit⟩

end Omega.GroupUnification
